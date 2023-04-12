/*-----------------------------------------------------------------------------
 *
 * ig_main.c
 *
 *
 *		AUTHOR: shemon & seokki
 *
 *
 *
 *-----------------------------------------------------------------------------
 */

#include "configuration/option.h"
#include "instrumentation/timing_instrumentation.h"
#include "provenance_rewriter/pi_cs_rewrites/pi_cs_main.h"
#include "provenance_rewriter/ig_rewrites/ig_main.h"
#include "provenance_rewriter/prov_utility.h"
#include "utility/string_utils.h"
#include "model/query_operator/query_operator.h"
#include "model/query_operator/query_operator_model_checker.h"
#include "model/query_operator/operator_property.h"
#include "mem_manager/mem_mgr.h"
#include "log/logger.h"
#include "model/node/nodetype.h"
#include "provenance_rewriter/prov_schema.h"
#include "model/list/list.h"
#include "model/set/set.h"
#include "model/expression/expression.h"
#include "model/set/hashmap.h"
#include "parser/parser_jp.h"
#include "provenance_rewriter/transformation_rewrites/transformation_prov_main.h"
#include "provenance_rewriter/semiring_combiner/sc_main.h"
#include "provenance_rewriter/coarse_grained/coarse_grained_rewrite.h"

#define LOG_RESULT(mes,op) \
    do { \
        INFO_OP_LOG(mes,op); \
        DEBUG_NODE_BEATIFY_LOG(mes,op); \
    } while(0)

static QueryOperator *rewriteIG_Operator (QueryOperator *op);
static QueryOperator *rewriteIG_Conversion (ProjectionOperator *op);
static QueryOperator *rewriteIG_Projection(ProjectionOperator *op);
static QueryOperator *rewriteIG_Join(JoinOperator *op);
static QueryOperator *rewriteIG_TableAccess(TableAccessOperator *op);

static Node *asOf;
static RelCount *nameState;
//static QueryOperator *provComputation;
//static ProvenanceType provType;
List *attrL = NIL;
List *attrR = NIL;


QueryOperator *
rewriteIG (ProvenanceComputation  *op)
{
//	// IG
//	provType = op->provType;

    START_TIMER("rewrite - IG rewrite");

    // unset relation name counters
    nameState = (RelCount *) NULL;

    DEBUG_NODE_BEATIFY_LOG("*************************************\nREWRITE INPUT\n"
            "******************************\n", op);

    //mark the number of table - used in provenance scratch
    markNumOfTableAccess((QueryOperator *) op);

    QueryOperator *rewRoot = OP_LCHILD(op);
    DEBUG_NODE_BEATIFY_LOG("rewRoot is:", rewRoot);

    // cache asOf
    asOf = op->asOf;

    // rewrite subquery under provenance computation
    rewriteIG_Operator(rewRoot);
    DEBUG_NODE_BEATIFY_LOG("before rewritten query root is switched:", rewRoot);

    // update root of rewritten subquery
    rewRoot = OP_LCHILD(op);

    // adapt inputs of parents to remove provenance computation
    switchSubtrees((QueryOperator *) op, rewRoot);
    DEBUG_NODE_BEATIFY_LOG("rewritten query root is:", rewRoot);

    STOP_TIMER("rewrite - IG rewrite");

    return rewRoot;
}


static QueryOperator *
rewriteIG_Operator (QueryOperator *op)
{
    QueryOperator *rewrittenOp;

    switch(op->type)
    {
    	case T_CastOperator:
        	FATAL_LOG("no rewrite implemented for operator ", nodeToString(op));
        	return NULL;
        case T_SelectionOperator:
        	FATAL_LOG("no rewrite implemented for operator ", nodeToString(op));
        	return NULL;
        case T_ProjectionOperator:
            rewrittenOp = rewriteIG_Projection((ProjectionOperator *) op);
            break;
        case T_AggregationOperator:
        	FATAL_LOG("no rewrite implemented for operator ", nodeToString(op));
        	return NULL;
        case T_JoinOperator:
            rewrittenOp = rewriteIG_Join((JoinOperator *) op);
            break;
        case T_SetOperator:
        	FATAL_LOG("no rewrite implemented for operator ", nodeToString(op));
        	return NULL;
        case T_TableAccessOperator:
            rewrittenOp = rewriteIG_TableAccess((TableAccessOperator *) op);
            break;
        case T_ConstRelOperator:
        	FATAL_LOG("no rewrite implemented for operator ", nodeToString(op));
        	return NULL;
        case T_DuplicateRemoval:
        	FATAL_LOG("no rewrite implemented for operator ", nodeToString(op));
        	return NULL;
        case T_OrderOperator:
        	FATAL_LOG("no rewrite implemented for operator ", nodeToString(op));
        	return NULL;
        case T_JsonTableOperator:
        	FATAL_LOG("no rewrite implemented for operator ", nodeToString(op));
        	return NULL;
        case T_NestingOperator:
        	FATAL_LOG("no rewrite implemented for operator ", nodeToString(op));
        	return NULL;
        default:
            FATAL_LOG("no rewrite implemented for operator ", nodeToString(op));
            return NULL;
    }

    if (isRewriteOptionActivated(OPTION_AGGRESSIVE_MODEL_CHECKING)){
        ASSERT(checkModel(rewrittenOp));
    }
    DEBUG_NODE_BEATIFY_LOG("rewritten query operators:", rewrittenOp);
    LOG_RESULT("rewritten query operators:", rewrittenOp);
    return rewrittenOp;
}


static QueryOperator *
rewriteIG_Conversion (ProjectionOperator *op)
{
	List *newProjExprs = NIL;
	List *attrNames = NIL;
	List *newNames = NIL;

	FOREACH(AttributeReference, a, op->projExprs)
	{
		if(isPrefix(a->name,"ig"))
		{
			if (a->attrType == DT_STRING)
			{
				StringToArray *toArray;
				Unnest *tounnest;
				Ascii *toAscii;

				toArray = createStringToArrayExpr((Node *) a, "NULL");
				tounnest = createUnnestExpr((Node *) toArray);
				toAscii = createAsciiExpr((Node *) tounnest);

				newProjExprs = appendToTailOfList(newProjExprs, toAscii);
			}
			else
			{
				newProjExprs = appendToTailOfList(newProjExprs, a);
			}
		}
		else
		{
			newProjExprs = appendToTailOfList(newProjExprs, a);
		}

	}

	op->projExprs = newProjExprs;

	// CREATING a projection to not feed ascii expression into aggregation
	int cnt = 0;
	List *projExprs = NIL;

	FOREACH(AttributeDef,a,op->op.schema->attrDefs)
	{
		projExprs = appendToTailOfList(projExprs,
				createFullAttrReference(a->attrName, 0, cnt, 0, a->dataType));

		attrNames = appendToTailOfList(attrNames, a->attrName);

		cnt++;
	}

	//create projection operator upon selection operator from select clause
	ProjectionOperator *po = createProjectionOp(projExprs, NULL, NIL, attrNames);
	addChildOperator((QueryOperator *) po, (QueryOperator *) op);
	// Switch the subtree with this newly created projection operator.
	switchSubtrees((QueryOperator *) op, (QueryOperator *) po);
	LOG_RESULT("Rewritten Projection Operator tree", po);

	// Creating aggregate operation
	// QueryOperator *o = copyObject((QueryOperator *) op);

	List *aggrs = NIL;
	List *groupBy = NIL;
	//List *attrNamesOriginal = NIL;
	attrNames = NIL;


	int i = 0;

	FOREACH(Node,n,newProjExprs)
	{
		if(isA(n,Ascii))
		{
			char *attrName = getAttrNameByPos((QueryOperator *) po, i);
			AttributeReference *ar = createAttrsRefByName((QueryOperator *) po, attrName);
			FunctionCall *sum = createFunctionCall("SUM", singleton(ar));
			aggrs = appendToTailOfList(aggrs,sum);

		}
		else
		{
			if(isA(n,AttributeReference))
			{
				groupBy = appendToTailOfList(groupBy,n);

			}

			if(isA(n,CastExpr))
			{
				CastExpr *ce = (CastExpr *) n;
				AttributeReference *ar = (AttributeReference *) ce->expr;
				groupBy = appendToTailOfList(groupBy, (Node *) ar);
			}
		}

		i++;
	}


	// CREATING NEW NAMES HERE FOR AGGREGATE OPERATOR
	FOREACH(AttributeReference, a, po->projExprs)
	{
		if(isPrefix(a->name, "ig") && a->attrType == DT_STRING)
		{
//			char *nn = CONCAT_STRINGS(a->name,"_agg");
			newNames = appendToTailOfList(newNames, a->name);
		}
	}

	FOREACH(AttributeReference, b, po->projExprs)
	{
		if(!isPrefix(b->name, "ig"))
		{
			newNames = appendToTailOfList(newNames, b->name);
		}
		else if(isPrefix(b->name, "ig") && b->attrType != DT_STRING)
		{
			newNames = appendToTailOfList(newNames, b->name);
		}
	}

//	// Create fake attribute names for aggregation output schema
//	for (i = 0; i < LIST_LENGTH(aggrs); i++)
//	{
//		attrNames = appendToTailOfList(attrNames, CONCAT_STRINGS("AGGR_", gprom_itoa(i)));
//	}
//	for (i = 0; i < LIST_LENGTH(groupBy); i++)
//	{
//		attrNames = appendToTailOfList(attrNames, CONCAT_STRINGS("GROUP_", gprom_itoa(i)));
//	}

	AggregationOperator *ao = createAggregationOp(aggrs, groupBy, NULL, NIL, newNames);
	addChildOperator((QueryOperator *) ao, (QueryOperator *) po);

	// Switch the subtree with this newly created projection operator.
	switchSubtrees((QueryOperator *) po, (QueryOperator *) ao);

	LOG_RESULT("Rewritten Aggregation Operator tree", ao);

	// CREATING THE NEW PROJECTION OPERATOR
	projExprs = NIL;
	cnt = 0;

	FOREACH(AttributeDef,a,ao->op.schema->attrDefs)
	{
		projExprs = appendToTailOfList(projExprs,
				createFullAttrReference(a->attrName, 0, cnt, 0, a->dataType));

		cnt++;
	}

	//create projection operator upon selection operator from select clause
	ProjectionOperator *newPo = createProjectionOp(projExprs, NULL, NIL, newNames);
	addChildOperator((QueryOperator *) newPo, (QueryOperator *) ao);

	// Switch the subtree with this newly created projection operator.
	switchSubtrees((QueryOperator *) ao, (QueryOperator *) newPo);
	LOG_RESULT("Rewritten Projection Operator tree", newPo);

	// CAST_EXPR
	newProjExprs = NIL;

	FOREACH(AttributeReference, a, newPo->projExprs)
	{
		if(a->attrType == DT_INT || a->attrType == DT_FLOAT)
		{
			CastExpr *cast;
			cast = createCastExpr((Node *) a, DT_FLOAT);  // TODO: change to bit10
			newProjExprs = appendToTailOfList(newProjExprs, cast);
		}
		else
			newProjExprs = appendToTailOfList(newProjExprs, a);
	}

	newPo->projExprs = newProjExprs;
	LOG_RESULT("Rewritten Projection Operator tree with CAST", newPo);

	// retrieve the original order of the projection attributes
	projExprs = NIL;
	newNames = NIL;


	FOREACH(AttributeDef,a,po->op.schema->attrDefs)
	{
		projExprs = appendToTailOfList(projExprs,
				createFullAttrReference(a->attrName, 0,
						getAttrPos((QueryOperator *) newPo, a->attrName), 0, a->dataType));

		newNames = appendToTailOfList(newNames, a->attrName);
	}

	ProjectionOperator *addPo = createProjectionOp(projExprs, NULL, NIL, newNames);
	addChildOperator((QueryOperator *) addPo, (QueryOperator *) newPo);

	// Switch the subtree with this newly created projection operator.
	switchSubtrees((QueryOperator *) newPo, (QueryOperator *) addPo);


    LOG_RESULT("Converted Operator tree", addPo);
	return (QueryOperator *) addPo;
}


static QueryOperator *
rewriteIG_Projection (ProjectionOperator *op)
{
    ASSERT(OP_LCHILD(op));
    DEBUG_LOG("REWRITE-IG - Projection");
    DEBUG_LOG("Operator tree \n%s", nodeToString(op));

    // rewrite child
    rewriteIG_Operator(OP_LCHILD(op));

    QueryOperator *child = OP_LCHILD(op);
 	switchSubtrees((QueryOperator *) op, child);
//    child->parents = NIL;

	List *newProjExpr = NIL;
	List *newAttrNames = NIL;
	int pos = 0;

	FOREACH(AttributeDef, a, child->schema->attrDefs)
	{
		newProjExpr = appendToTailOfList(newProjExpr,
				 createFullAttrReference(a->attrName, 0, pos, 0, a->dataType));

		newAttrNames = appendToTailOfList(newAttrNames, a->attrName);
		pos++;
	}

	ProjectionOperator *newProj = createProjectionOp(newProjExpr, NULL, NIL, newAttrNames);

    List *attrNames = NIL;
    newProjExpr = NIL;
    pos = 0;
    int temp = 0;
//TESTING CONCAT
//GOAL :
//SELECT CONCAT('-o-', county, '-c-', year , '-y-', dayswaqi , '-d-', maqi, '-m-') as anno from owned

	    FOREACH(AttributeReference, n, newProj->projExprs)
	    {

	    	if(temp == 0)
	    	{
	    		//ADDING DATASET NAME
				newProjExpr = appendToTailOfList(newProjExpr,
						createFullAttrReference("-owned-", n->fromClauseItem, pos, 0, n->attrType));
				temp++;
	    	}

	    	else if (isPrefix(n->name, "ig"))
	    	{
//	    		n->name = substr(n->name, 3, 4);
//	    		n->name = "test";
	    		newProjExpr = appendToTailOfList(newProjExpr, n);
//	    		newProjExpr = appendToTailOfList(newProjExpr,
//	    				createFullAttrReference(substr(n->name, 3, 4), n->fromClauseItem, pos, 0, n->attrType));

	    		//POS HERE MIGHT BE WRONG
	    		newProjExpr = appendToTailOfList(newProjExpr,
	    			    				createFullAttrReference(substr(n->name, 14, 16), n->fromClauseItem, pos, 0, n->attrType));
	    		pos++;
	    		newProjExpr = LIST_MAKE(concatExprList(newProjExpr));
//	    		newProjExpr = LIST_MAKE(concatExprs((Node *)"-test-"));
//	    		n->name = substr(n->name, 2,5);
//	    		newProjExpr = appendToTailOfList(newProjExpr, n);
//	    		newProjExpr = appendToTailOfList(newProjExpr, "-O-");
//	    		newProjExpr = appendToTailOfList(newProjExpr, substr(n->name, 2,5));

//	    		newProjExpr = LIST_MAKE(concatExprList(newProjExpr));
//	    		makeNode()
//	    		createnodeKeyValue

	    	}
//	    	else
//	    	{
//	    		newProjExpr = appendToTailOfList(newProjExpr, n);
//	    	}

			attrNames = appendToTailOfList(attrNames, n->name);
	    }

//	    newProjExpr = LIST_MAKE(concatExprList(newProjExpr));
//	    newProjExpr = LIST_MAKE(concatExprs(newProjExpr));
	    ProjectionOperator *concat = createProjectionOp(newProjExpr, NULL, NIL, attrNames);
	    LOG_RESULT("TESTING CONCAT EXPRESSION LIST", concat);

	    attrNames = NIL;
	    newProjExpr = NIL;
//TESTING CONCAT

////TESTING CONCAT 1
//
//	    FOREACH(AttributeReference, n, newProj->projExprs)
//	    {
//	    	if (isPrefix(n->name, "ig"))
//	    	{
//	    		newProjExpr = appendToTailOfList(newProjExpr, n);
//	    		newProjExpr = appendToTailOfList(newProjExpr, "test");
//	    		newProjExpr = LIST_MAKE(concatExprList(newProjExpr));
////	    		newProjExpr = appendToTailOfList(LIST_MAKE(concatExprList(newProjExpr)), "test");
////	    				substr(n->name, 2,5));
//
//	    	}
////	    	else
////	    	{
////	    		newProjExpr = appendToTailOfList(newProjExpr, n);
////	    	}
//
//			attrNames = appendToTailOfList(attrNames, n->name);
//	    }
//
//
//	    ProjectionOperator *concat1 = createProjectionOp(newProjExpr, NULL, NIL, attrNames);
//	    LOG_RESULT("TESTING CONCAT EXPRESSION LIST - 1", concat1);
//
//	    attrNames = NIL;
//	    newProjExpr = NIL;
////TESTING CONCAT




    int i = 0; // position of the attribute
//    int checkPoint = LIST_LENGTH(attrL) - 1; // point where the attributes belong to shared data
//    AttributeDef *a = NULL;

    List *LprojExprs = NIL;
    List *RprojExprs = NIL;
    List *LattrNames = NIL;
    List *RattrNames = NIL;
    HashMap *nameToIgAttrName = NEW_MAP(Constant, Constant);
    int lenL = LIST_LENGTH(attrL) - 1;
    int l = 0;
    int posOfIgL = LIST_LENGTH(attrL) / 2;

    FOREACH(AttributeDef,a,attrL)
    {
    	if(!isPrefix(a->attrName,"ig"))
    	{
        	char *key = a->attrName;
        	AttributeDef *igA = (AttributeDef *) getNthOfListP(attrL,posOfIgL);
        	char *value = igA->attrName;

        	ADD_TO_MAP(nameToIgAttrName,createStringKeyValue(key,value));
        	posOfIgL++;
    	}
    }


    FOREACH(AttributeReference, n, newProj->projExprs)
    {
    	if(l <= lenL)
    	{
    		LprojExprs = appendToTailOfList(LprojExprs, n);
			LattrNames = appendToTailOfList(LattrNames, n->name);
			l++;
    	}
    }

    ProjectionOperator *Lop = createProjectionOp(LprojExprs, NULL, NIL, LattrNames);
    LOG_RESULT("TESTING LEFT LIST", Lop);
    l = 0;
    FOREACH(AttributeReference, n, newProj->projExprs)
       {
    	if(l > lenL)
    	{
			RprojExprs = appendToTailOfList(RprojExprs, n);
			RattrNames = appendToTailOfList(RattrNames, n->name);
			l++;
    	}
    	else
    	{
    		l++;
    	}
       }


    ProjectionOperator *Rop = createProjectionOp(RprojExprs, NULL, NIL, RattrNames);
    LOG_RESULT("TESTING RIGHT LIST", Rop);

    //HashMap *nameToAttrDef = NEW_MAP(List* , List*);

    //TESTING CONCAT
    //GOAL :
    //SELECT CONCAT('-o-', county, '-c-', year , '-y-', dayswaqi , '-d-', maqi, '-m-') as anno from owned

    	temp = 0;
		FOREACH(AttributeReference, n, Lop->projExprs)
		{

			if(temp == 0)
			{
				newProjExpr = appendToTailOfList(newProjExpr,
						createFullAttrReference("-owned-", n->fromClauseItem, pos, 0, n->attrType));
				temp++;
			}

			else if (isPrefix(n->name, "ig"))
			{
				newProjExpr = appendToTailOfList(newProjExpr, n);
				newProjExpr = appendToTailOfList(newProjExpr,
						createFullAttrReference((substr(n->name, 14, 16)), n->fromClauseItem, pos, 0, n->attrType));
						//(createConstString(substr(n->name, 14, 16))

						pos++;
				newProjExpr = LIST_MAKE(concatExprList(newProjExpr));

			}
			attrNames = appendToTailOfList(attrNames, n->name);
		}

		ProjectionOperator *Lconcat = createProjectionOp(newProjExpr, NULL, NIL, attrNames);
		LOG_RESULT("TESTING LEFT EXPRESSION LIST", Lconcat);

		attrNames = NIL;
		newProjExpr = NIL;
		temp = 0;

		FOREACH(AttributeReference, n, Rop->projExprs)
		{

			if(temp == 0)
			{
				newProjExpr = appendToTailOfList(newProjExpr,
						createFullAttrReference("-shared-", n->fromClauseItem, pos, 0, n->attrType));
				temp++;
			}

			else if (isPrefix(n->name, "ig"))
			{
				newProjExpr = appendToTailOfList(newProjExpr, n);
				newProjExpr = appendToTailOfList(newProjExpr,
						createFullAttrReference((substr(n->name, 14, 16)), n->fromClauseItem, pos, 0, n->attrType));
						//(createConstString(substr(n->name, 14, 16)),
						pos++;
				newProjExpr = LIST_MAKE(concatExprList(newProjExpr));

			}
			attrNames = appendToTailOfList(attrNames, n->name);
		}
		ProjectionOperator *Rconcat = createProjectionOp(newProjExpr, NULL, NIL, attrNames);
		LOG_RESULT("TESTING RIGHT EXPRESSION LIST", Rconcat);

		attrNames = NIL;
		newProjExpr = NIL;

//int llist = 1;
//int rlist = 1;

//// METHOD 2 To add expressions

    FOREACH(AttributeReference, n, Lop->projExprs)
    {
    	if(isPrefix(n->name, "ig"))
		{
        	FOREACH(AttributeReference, n1, Rop->projExprs) // right list
    		{
        		if(isPrefix(n1->name, "ig"))
        		{
        			if(strcmp(strrchr(n->name, '_'), strrchr(n1->name, '_')) == 0)
//					if(strCompare(strEndTok(n->name, "_"), strEndTok(n1->name, "_")) == 0)
					{
        				Node *cond = (Node *) createIsNullExpr((Node *) n);
						Node *els  = (Node *) createAttributeReference(n->name);
						Node *then = (Node *) createAttributeReference(n1->name);
						CaseWhen *caseWhen = createCaseWhen(cond, then);
						CaseExpr *caseExpr = createCaseExpr(NULL, singleton(caseWhen), els);
						newProjExpr = appendToTailOfList(newProjExpr, caseExpr);
						attrNames = appendToTailOfList(attrNames, n->name);

						Node *cond1 = (Node *) createIsNullExpr((Node *) n1);
						Node *els1  = (Node *) createAttributeReference(n1->name);
						Node *then1 = (Node *) createAttributeReference(n->name);
						CaseWhen *caseWhen1 = createCaseWhen(cond1, then1);
						CaseExpr *caseExpr1 = createCaseExpr(NULL, singleton(caseWhen1), els1);
						newProjExpr = appendToTailOfList(newProjExpr, caseExpr1);
						attrNames = appendToTailOfList(attrNames, n->name);
					}
        		}
    		}
		}
		else if(!isPrefix(n->name, "ig"))
		{
			newProjExpr = appendToTailOfList(newProjExpr, n);
			attrNames = appendToTailOfList(attrNames, n->name);
		}

		i++;

    }

//
//
//
//    FOREACH(AttributeReference, n, newProj->projExprs)
//    {
//    		if (isPrefix(n->name, "ig"))
//			{
//
//				Node *cond = (Node *) createIsNullExpr((Node *) n);
//				//Node *then = (Node *) createConstInt(0);
//				//Node *els = (Node *) createConstInt(1);
//				Node *els = (Node *) createAttributeReference(n->name);
//
//				if (i <= checkPoint)
//				{
//					a = (AttributeDef *) getNthOfListP(attrR, i);
//				}
//				else
//				{
//					int j = i - checkPoint - 1; // index for retrieving the correspond attribute from shared (owned) table
//					a = (AttributeDef *) getNthOfListP(attrL, j);
//				}
//
//				Node *then = (Node *) createAttributeReference(a->attrName);
//
//				CaseWhen *caseWhen = createCaseWhen(cond, then);
//				CaseExpr *caseExpr = createCaseExpr(NULL, singleton(caseWhen), els);
//
//	//    		caseExprs = appendToTailOfList(caseExprs, (List *) caseExpr);
	//    		attrs = appendToTailOfList(attrs, CONCAT_STRINGS("use_",n->name));
//
//				newProjExpr = appendToTailOfList(newProjExpr, caseExpr);
//
//
//			}
//			else
//			{
//				newProjExpr = appendToTailOfList(newProjExpr, n);
//			}
//
//			attrNames = appendToTailOfList(attrNames, n->name);
//
//			i++;
//
//
//    }


//    attrNames = concatTwoLists(attrNames, attrs);
//    newList = concatTwoLists(op->projExprs, caseExprs);

    ProjectionOperator *op1 = createProjectionOp(newProjExpr, NULL, NIL, attrNames);
    LOG_RESULT("TESTING CASE EXPRESSIONS", op1);

//    addChildOperator((QueryOperator *) newProjExpr, (QueryOperator *) child);
//    switchSubtrees((QueryOperator *) child, (QueryOperator *) newProjExpr);
//
// 	  LOG_RESULT("Rewritten Projection Operator tree", newProjExpr);
//    return (QueryOperator *) newProjExpr;

	addChildOperator((QueryOperator *) newProj, (QueryOperator *) child);
	switchSubtrees((QueryOperator *) child, (QueryOperator *) newProj);

	LOG_RESULT("Rewritten Projection Operator tree", newProj);
    return (QueryOperator *) newProj;

}

static QueryOperator *
rewriteIG_Join (JoinOperator *op)
{
    DEBUG_LOG("REWRITE-IG - Join");

//    QueryOperator *o = (QueryOperator *) op;
    QueryOperator *lChild = OP_LCHILD(op);
    QueryOperator *rChild = OP_RCHILD(op);

    lChild = rewriteIG_Operator(lChild);
    rChild = rewriteIG_Operator(rChild);

	// update the attribute def for join operator
    List *lAttrDefs = copyObject(getNormalAttrs(lChild));
    List *rAttrDefs = copyObject(getNormalAttrs(rChild));

    attrL = copyObject(lAttrDefs);
    attrR = copyObject(rAttrDefs);

    List *newAttrDefs = CONCAT_LISTS(lAttrDefs,rAttrDefs);
    op->op.schema->attrDefs = copyObject(newAttrDefs);
    makeAttrNamesUnique((QueryOperator *) op);

	LOG_RESULT("Rewritten Join Operator tree",op);
    return (QueryOperator *) op;
}


static QueryOperator *
rewriteIG_TableAccess(TableAccessOperator *op)
{
	List *attrNames = NIL;
	List *projExpr = NIL;
	List *newProjExprs = NIL;
	int relAccessCount = getRelNameCount(&nameState, op->tableName);
	int cnt = 0;

	DEBUG_LOG("REWRITE-IG - Table Access <%s> <%u>", op->tableName, relAccessCount);

	// copy any as of clause if there
	if (asOf)
		op->asOf = copyObject(asOf);

	// normal attributes
	FOREACH(AttributeDef, attr, op->op.schema->attrDefs)
	{
		attrNames = appendToTailOfList(attrNames, strdup(attr->attrName));
		projExpr = appendToTailOfList(projExpr, createFullAttrReference(attr->attrName, 0, cnt, 0, attr->dataType));
		cnt++;
	}

	// ig attributes
    cnt = 0;
    char *newAttrName;
    newProjExprs = copyObject(projExpr);

    FOREACH(AttributeDef, attr, op->op.schema->attrDefs)
    {
    	newAttrName = getIgAttrName(op->tableName, attr->attrName, relAccessCount);
    	attrNames = appendToTailOfList(attrNames, newAttrName);

   		projExpr = appendToTailOfList(projExpr, createFullAttrReference(attr->attrName, 0, cnt, 0, attr->dataType));
    	cnt++;
    }

    List *newIgPosList = NIL;
    CREATE_INT_SEQ(newIgPosList, cnt, (cnt * 2) - 1, 1);

	ProjectionOperator *po = createProjectionOp(projExpr, NULL, NIL, attrNames);

	// set ig attributes and property
	po->op.igAttrs = newIgPosList;
	SET_BOOL_STRING_PROP((QueryOperator *) po, PROP_PROJ_IG_ATTR_DUP);

	addChildOperator((QueryOperator *) po, (QueryOperator *) op);
//	op->op.parents = singleton(proj);

	// Switch the subtree with this newly created projection operator.
    switchSubtrees((QueryOperator *) op, (QueryOperator *) po);

    DEBUG_LOG("table access after adding additional attributes for ig: %s", operatorToOverviewString((Node *) po));

	// add projection expressions for ig attrs
	FOREACH_INT(a, po->op.igAttrs)
	{
		AttributeDef *att = getAttrDef((QueryOperator *) po,a);
		newProjExprs = appendToTailOfList(newProjExprs,
				 createFullAttrReference(att->attrName, 0, a, 0, att->dataType));
	}

	ProjectionOperator *newPo = createProjectionOp(newProjExprs, NULL, NIL, attrNames);
	addChildOperator((QueryOperator *) newPo, (QueryOperator *) po);

	// Switch the subtree with this newly created projection operator.
    switchSubtrees((QueryOperator *) po, (QueryOperator *) newPo);

    DEBUG_LOG("table access after adding ig attributes to the schema: %s", operatorToOverviewString((Node *) newPo));
    LOG_RESULT("Rewritten TableAccess Operator tree", newPo);
    return rewriteIG_Conversion(newPo);
}
