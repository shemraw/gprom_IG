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
#include "provenance_rewriter/ig_rewrites/ig_functions.h" //------------------
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

//#include "src/provenance_rewriter/ig_rewrites/ig_functions.c"

#define LOG_RESULT(mes,op) \
    do { \
        INFO_OP_LOG(mes,op); \
        DEBUG_NODE_BEATIFY_LOG(mes,op); \
    } while(0)

#define INDEX "i_"
#define IG_PREFIX "ig_"
#define VALUE_IG "value_"
#define INTEG_SUFFIX "_integ"
#define HAMMING_PREFIX "hamming_"
#define PATTERN_IG "pattern_IG"
#define TOTAL_DIST "Total_Distance"
#define AVG_DIST "Average_Distance"
#define COVERAGE "coverage"
#define INFORMATIVENESS "informativeness"
#define FSCORE "f_score"


static QueryOperator *rewriteIG_Operator (QueryOperator *op);
static QueryOperator *rewriteIG_Conversion (ProjectionOperator *op);
static QueryOperator *rewriteIG_Projection(ProjectionOperator *op);
static QueryOperator *rewriteIG_Selection(SelectionOperator *op);
static QueryOperator *rewriteIG_Join(JoinOperator *op);
static QueryOperator *rewriteIG_TableAccess(TableAccessOperator *op);
//static ProjectionOperator *rewriteIG_SumExprs(ProjectionOperator *op);
//static ProjectionOperator *rewriteIG_HammingFunctions(ProjectionOperator *op);

static Node *asOf;
static RelCount *nameState;
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

    QueryOperator *newRoot = OP_LCHILD(op);
//    QueryOperator *rewRoot = (QueryOperator *) op;
    DEBUG_NODE_BEATIFY_LOG("rewRoot is:", newRoot);

    // cache asOf
    asOf = op->asOf;

    // rewrite subquery under provenance computation
    rewriteIG_Operator(newRoot);
    DEBUG_NODE_BEATIFY_LOG("before rewritten query root is switched:", newRoot);

    // update root of rewritten subquery
    newRoot = OP_LCHILD(op);

    // adapt inputs of parents to remove provenance computation
    switchSubtrees((QueryOperator *) op, newRoot);
    DEBUG_NODE_BEATIFY_LOG("rewritten query root is:", newRoot);

    STOP_TIMER("rewrite - IG rewrite");

    return newRoot;
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
        	rewrittenOp = rewriteIG_Selection((SelectionOperator *) op);
        	break;
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
    return rewrittenOp;
}

static QueryOperator *
rewriteIG_Selection (SelectionOperator *op) //where clause
{
    ASSERT(OP_LCHILD(op));

    DEBUG_LOG("REWRITE-PICS - Selection");
    DEBUG_LOG("Operator tree \n%s", nodeToString(op));

    //add semiring options
    QueryOperator *child = OP_LCHILD(op);

//    addSCOptionToChild((QueryOperator *) op,child);

    // rewrite child first
    rewriteIG_Operator(child);
//  switchSubtrees((QueryOperator *) op, child); // child here has join property

    List *tempExpr = NIL;
    List *tempNames = NIL;
    int posTemp = 0;

    FOREACH(AttributeDef, a, child->schema->attrDefs)
 	{
 		tempExpr = appendToTailOfList(tempExpr,
 				 createFullAttrReference(a->attrName, 0, posTemp, 0, a->dataType));

 		tempNames = appendToTailOfList(tempNames, a->attrName);
 		posTemp++;
 	}

    // update selection
	Operator *cond = (Operator *) op->cond;
//	boolean isConds = FALSE;

	FOREACH(Node, n, cond->args)
	{
		if(isA(n,AttributeReference))
		{
			AttributeReference *ar = (AttributeReference *) n;
			int attrPos = getAttrPos(child, ar->name);
			ar->attrPosition = attrPos;
		}

		if(isA(n,Operator))
		{
			Operator *o = (Operator *) n;
			FOREACH(Node, n, o->args)
			{
				if(isA(n,AttributeReference))
				{
					AttributeReference *ar = (AttributeReference *) n;
					int attrPos = getAttrPos(child, ar->name);
					ar->attrPosition = attrPos;
				}
			}
//			else
//			{
//				FATAL_LOG("!! Not yet implemented !!", nodeToString(op));
//			}
		}
	}

	op->op.schema->attrDefs = child->schema->attrDefs;

//	SelectionOperator *so = createSelectionOp((Node *) cond, child, NIL, getAttrNames(child->schema));
//	addParent(child, (QueryOperator *) so);

	// if there is PROP_JOIN_ATTRS_FOR_HAMMING set then copy over the properties to the new proj op
	if(HAS_STRING_PROP(child, PROP_JOIN_ATTRS_FOR_HAMMING))
	{
		SET_STRING_PROP(op, PROP_JOIN_ATTRS_FOR_HAMMING,
				copyObject(GET_STRING_PROP(child, PROP_JOIN_ATTRS_FOR_HAMMING)));
	}

// 	ProjectionOperator *tempProj = createProjectionOp(tempExpr, NULL, NIL, tempNames);
//// 	op->op.schema->attrDefs = tempProj->op.schema->attrDefs;
//
// 	// comment it out and check
// 	addChildOperator((QueryOperator *) tempProj, (QueryOperator *) op);
// 	switchSubtrees((QueryOperator *) op, (QueryOperator *) tempProj);

// 	// if there is PROP_JOIN_ATTRS_FOR_HAMMING set then copy over the properties to the new proj op
//	if(HAS_STRING_PROP(child, PROP_JOIN_ATTRS_FOR_HAMMING))
//	{
//		SET_STRING_PROP(tempProj, PROP_JOIN_ATTRS_FOR_HAMMING,
//				copyObject(GET_STRING_PROP(child, PROP_JOIN_ATTRS_FOR_HAMMING)));
//	}

    LOG_RESULT("Rewritten Selection Operator tree", op);
    return (QueryOperator *) op;
}

//rewriteIG_Conversion
static QueryOperator *
rewriteIG_Conversion (ProjectionOperator *op)
{
	List *newProjExprs = NIL;
	List *attrNames = NIL;

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

		if(isPrefix(a->attrName, "ig") && a->dataType == DT_STRING)
		{
			a->dataType = DT_INT;
		}

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

	List *aggrs = NIL;
	List *groupBy = NIL;
	List *newNames = NIL;
	List *aggrNames = NIL;
	List *groupByNames = NIL;
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
			aggrNames = appendToTailOfList(aggrNames,attrName);
		}
		else
		{
			if(isA(n,AttributeReference))
			{
				groupBy = appendToTailOfList(groupBy,n);

				AttributeReference *ar = (AttributeReference *) n;
				groupByNames = appendToTailOfList(groupByNames,(ar->name));
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

	newNames = CONCAT_LISTS(aggrNames, groupByNames);
	AggregationOperator *ao = createAggregationOp(aggrs, groupBy, NULL, NIL, newNames);

	addChildOperator((QueryOperator *) ao, (QueryOperator *) po);
	// Switch the subtree with this newly created projection operator.
	switchSubtrees((QueryOperator *) po, (QueryOperator *) ao);

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

	// CAST_EXPR
	newProjExprs = NIL;

	FOREACH(AttributeReference, a, newPo->projExprs)
	{
		if(isPrefix(a->name, "ig"))
		{

				CastExpr *castInt;
				CastExpr *cast;
				castInt = createCastExpr((Node *) a, DT_INT);
				cast = createCastExpr((Node *) castInt, DT_BIT10);

				newProjExprs = appendToTailOfList(newProjExprs, cast);
		}
		else
			newProjExprs = appendToTailOfList(newProjExprs, a);
	}

	newPo->projExprs = newProjExprs;

	// matching the datatype of attribute def in the projection
	FOREACH(AttributeDef, a, newPo->op.schema->attrDefs)
	{
		if(isPrefix(a->attrName,"ig"))
		{
			a->dataType = DT_BIT10;
		}
	}

//	retrieve the original order of the projection attributes
	projExprs = NIL;
	newNames = NIL;


	FOREACH(AttributeDef,a,po->op.schema->attrDefs)
	{
		projExprs = appendToTailOfList(projExprs,
				createFullAttrReference(a->attrName, 0,
						getAttrPos((QueryOperator *) newPo, a->attrName), 0,
						isPrefix(a->attrName,"ig") ? DT_BIT10 : a->dataType));

		newNames = appendToTailOfList(newNames, a->attrName);
	}


	ProjectionOperator *addPo = createProjectionOp(projExprs, NULL, NIL, newNames);;

	// Getting Table name and length of table name here
	char *tblName = NULL;
	FOREACH(AttributeReference, n, addPo->projExprs)
	{
		if(isPrefix(n->name, IG_PREFIX))
		{
			int len1 = strlen(n->name);
			int len2 = strlen(strrchr(n->name, '_'));
			int len = len1 - len2 - 1;
			tblName = substr(n->name, 8, len);
//			break;
		}
	}

	int temp = 0;
	int tblLen = strlen(tblName);

	List *newProjExpr = NIL;
	List *newProjExpr1 = NIL;
	List *newProjExpr2 = NIL;


	// Getting original attributes
	FOREACH(AttributeReference, n, addPo->projExprs)
	{
		newProjExpr1 = appendToTailOfList(newProjExpr1, n);
		attrNames = appendToTailOfList(attrNames, n->name);
	}

	// Creating _anno Attribute
	FOREACH(AttributeReference, n, addPo->projExprs)
	{

		if(temp == 0)
		{
			newProjExpr = appendToTailOfList(newProjExpr, createConstString(tblName));
			temp++;
		}
		else if (isPrefix(n->name, IG_PREFIX))
		{
			CastExpr *cast;
			cast = createCastExpr((Node *) n, DT_STRING);
			newProjExpr = appendToTailOfList(newProjExpr, cast);

			//this adds first 3 letter for the variable in concat
			int end = strlen(strrchr(n->name, '_'));

			newProjExpr = appendToTailOfList(newProjExpr,
					createConstString((substr(n->name, 9 + tblLen, 9 + tblLen + end - 2))));
		}
	}

	attrNames = appendToTailOfList(attrNames, CONCAT_STRINGS(tblName, "_anno"));
	newProjExpr = LIST_MAKE(createOpExpr("||", newProjExpr));
	newProjExpr2 = concatTwoLists(newProjExpr1, newProjExpr);

	ProjectionOperator *concat = createProjectionOp(newProjExpr2, NULL, NIL, attrNames);

	addChildOperator((QueryOperator *) concat, (QueryOperator *) newPo);

	// Switch the subtree with this newly created projection operator.
	switchSubtrees((QueryOperator *) newPo, (QueryOperator *) concat);

    LOG_RESULT("Converted Operator tree", concat);
	return (QueryOperator *) concat;


}

//rewriteIG_SumExprs
static ProjectionOperator *
rewriteIG_SumExprs (ProjectionOperator *hammingvalue_op)
{
    ASSERT(OP_LCHILD(hammingvalue_op));
    DEBUG_LOG("REWRITE-IG - Computing rowIG");
    DEBUG_LOG("Operator tree \n%s", nodeToString(hammingvalue_op));
	// Adding Sum Rows and Avg Rows function
	int posV = 0;
	List *sumlist = NIL;
	Node *sumExpr = NULL;
	Node *avgExpr = NULL;
	List *sumExprs = NIL;
	List *sumNames = NIL;

	FOREACH(AttributeDef, a, hammingvalue_op->op.schema->attrDefs)
	{
		if(isPrefix(a->attrName, VALUE_IG))
		{
			AttributeReference *ar = createFullAttrReference(a->attrName, 0, posV,0, a->dataType);
			sumExprs = appendToTailOfList(sumExprs, ar);
			sumNames = appendToTailOfList(sumNames, a->attrName);
			sumlist = appendToTailOfList(sumlist, ar);
			posV++;
		}
		else
		{
			AttributeReference *ar = createFullAttrReference(a->attrName, 0, posV,0, a->dataType);
			sumExprs = appendToTailOfList(sumExprs, ar);
			sumNames = appendToTailOfList(sumNames, a->attrName);
			posV++;
		}

	}

	sumExpr = (Node *) (createOpExpr("+", sumlist));
	sumExprs = appendToTailOfList(sumExprs, sumExpr);
	sumNames = appendToTailOfList(sumNames, strdup(TOTAL_DIST));

	// Just tesing Average Expression Just in Case if we need it later in future
	List *origAttrs = (List *) GET_STRING_PROP((QueryOperator *) hammingvalue_op, IG_PROP_ORIG_ATTR);
	avgExpr = (Node *) (createOpExpr("/", LIST_MAKE(createOpExpr("+", sumlist), createConstInt(LIST_LENGTH(origAttrs)))));
	sumExprs = appendToTailOfList(sumExprs, avgExpr);
	sumNames = appendToTailOfList(sumNames, strdup(AVG_DIST));

	ProjectionOperator *sumrows = createProjectionOp(sumExprs, NULL, NIL, sumNames);
	//LOG_RESULT("TESTING SUM_AVG_ROWS FUNCTION", sumrows);

	addChildOperator((QueryOperator *) sumrows, (QueryOperator *) hammingvalue_op);
	switchSubtrees((QueryOperator *) hammingvalue_op, (QueryOperator *) sumrows);

	return sumrows;

}

//rewriteIG_HammingFunctions
static ProjectionOperator *
rewriteIG_HammingFunctions (ProjectionOperator *newProj)
{
    ASSERT(OP_LCHILD(newProj));
    DEBUG_LOG("REWRITE-IG - Hamming Computation");
    DEBUG_LOG("Operator tree \n%s", nodeToString(newProj));

    QueryOperator *child = OP_LCHILD(newProj);
    HashMap *nameToIgAttrOpp = NEW_MAP(Constant, Node);
    HashMap *nameToIgAttrRef = NEW_MAP(Constant, Node);

    // collect corresponding attributes of owned data
    int pos = 0;

    FOREACH(AttributeDef,a,attrL)
	{
    	if(isPrefix(a->attrName,IG_PREFIX))
    	{
//    		char *attrName = a->attrName;

    		//TODO: search corresponding attributes
    		AttributeDef *ar = (AttributeDef *) getNthOfListP(attrR,pos);
    		char *corrAttrName = ar->attrName;

    		// store the corresponding ig attribute names in shared
    		Node *arRef = (Node *) getAttrRefByName((QueryOperator *) child, corrAttrName);
    		MAP_ADD_STRING_KEY(nameToIgAttrOpp, a->attrName, arRef);

    		// store the ig attributes' reference
    		Node *aRef = (Node *) getAttrRefByName((QueryOperator *) child, a->attrName);
			MAP_ADD_STRING_KEY(nameToIgAttrRef, a->attrName, aRef);
    	}

    	pos++;
	}

    // collect corresponding attributes of shared data
    pos = 0;

    FOREACH(AttributeDef,a,attrR)
	{
    	if(isPrefix(a->attrName,IG_PREFIX))
    	{
//    		char *attrName = a->attrName;

    		//TODO: search corresponding attributes
    		AttributeDef *al = (AttributeDef *) getNthOfListP(attrL,pos);
    		char *corrAttrName = al->attrName;

    		// store the corresponding ig attribute names in shared
    		Node *alRef = (Node *) getAttrRefByName((QueryOperator *) child, corrAttrName);
    		MAP_ADD_STRING_KEY(nameToIgAttrOpp, a->attrName, alRef);

    		// store the ig attributes' reference
			Node *aRef = (Node *) getAttrRefByName((QueryOperator *) child, a->attrName);
			MAP_ADD_STRING_KEY(nameToIgAttrRef, a->attrName, aRef);
    	}

    	pos++;
	}


    // create provenance columns using case when
//    List *commonAttrNames = (List *) GET_STRING_PROP((QueryOperator *) newProj, IG_PROP_NON_JOIN_COMMON_ATTR);
    List *commonAttrNamesR = (List *) GET_STRING_PROP((QueryOperator *) newProj, IG_PROP_NON_JOIN_COMMON_ATTR_R);
	List *joinAttrNames = (List *) GET_STRING_PROP((QueryOperator *) newProj, IG_PROP_JOIN_ATTR);
	List *joinAttrNamesR = (List *) GET_STRING_PROP((QueryOperator *) newProj, IG_PROP_JOIN_ATTR_R);
	List *newProjExprs = NIL;
	pos = 0;

    FOREACH(AttributeDef, a, newProj->op.schema->attrDefs)
    {
//    	AttributeReference *origIgInteg = (AttributeReference *) getAttrRefByPos(newProj,pos);
		Node *n = (Node *) getNthOfListP(newProj->projExprs,pos);
		AttributeReference *origIgInteg = NULL;

		Node *cond = NULL;
		Node *then = NULL;
		Node *els = NULL;
		CaseWhen *caseWhen = NULL;
		CaseExpr *caseExpr = NULL;

    	// search corresponding attribute for integ ig column
    	if(isPrefix(a->attrName,IG_PREFIX))
    	{
    		if(isSuffix(a->attrName,INTEG_SUFFIX))
    		{
        		if(isA(n,AttributeReference))
        		{
        			origIgInteg = (AttributeReference *) n;
            		char *igOrigNameInteg = origIgInteg->name;

            		if(MAP_HAS_STRING_KEY(nameToIgAttrOpp, igOrigNameInteg))
        			{
        				AttributeReference *corrIgExpr =
        						(AttributeReference *) MAP_GET_STRING(nameToIgAttrOpp, igOrigNameInteg);

        				// for join attributes
        				if(searchListNode(joinAttrNames, (Node *) createConstString(igOrigNameInteg)))
        				{
        					cond = (Node *) createIsNullExpr((Node *) origIgInteg);
        					then = (Node *) corrIgExpr;
        					els = (Node *) origIgInteg;

        					caseWhen = createCaseWhen(cond, then);
        					caseExpr = createCaseExpr(NULL, singleton(caseWhen), els);
        				}
        				else
        				{
        //					// common attributes
        //					if(searchListString(commonAttrNames))
        //					{
        						cond = (Node *) createIsNullExpr((Node *) origIgInteg);
        						then = (Node *) createCastExpr((Node *) createConstInt(0), DT_BIT10);
        						els = (Node *) origIgInteg;

        						caseWhen = createCaseWhen(cond, then);
        						caseExpr = createCaseExpr(NULL, singleton(caseWhen), els);
        //					}
        //					// non-common attributes
        //					else
        //					{
        //						cond = (Node *) createIsNullExpr((Node *) origIgInteg);
        //						then = (Node *) createCastExpr((Node *) createConstInt(0), DT_BIT10);
        //						els = (Node *) origIgInteg;
        //
        //						CaseWhen *caseWhen = createCaseWhen(cond, then);
        //						CaseExpr *caseExpr = createCaseExpr(NULL, caseWhen, els);
        //						origIgInteg = caseExpr;
        //					}
        				}

        				newProjExprs = appendToTailOfList(newProjExprs,caseExpr);
        			}
        		}
        		else
        	    	newProjExprs = appendToTailOfList(newProjExprs,n);
    		}

        	// apply case when for original ig columns
        	if(!isSuffix(a->attrName,INTEG_SUFFIX))
        	{
        		origIgInteg = (AttributeReference *) n;
        		char *igOrigNameInteg = origIgInteg->name;

//        		// ig attributes from owned
//        		if(searchListNode(commonAttrNames, (Node *) createConstString(igOrigNameInteg)) ||
//        				searchListNode(joinAttrNames, (Node *) createConstString(igOrigNameInteg)))
//        		{
//    				cond = (Node *) createIsNullExpr((Node *) origIgInteg);
//    				then = (Node *) createCastExpr((Node *) createConstInt(0), DT_BIT10);
//    				els = (Node *) origIgInteg;
//
//    				caseWhen = createCaseWhen(cond, then);
//    				caseExpr = createCaseExpr(NULL, singleton(caseWhen), els);
//        		}
//        		// non-common attributes
//        		if(!searchListNode(commonAttrNames, (Node *) createConstString(igOrigNameInteg)) &&
//        				!searchListNode(joinAttrNames, (Node *) createConstString(igOrigNameInteg)))
//        		{
//    				cond = (Node *) createIsNullExpr((Node *) origIgInteg);
//    				then = (Node *) createCastExpr((Node *) createConstInt(0), DT_BIT10);
//    				els = (Node *) origIgInteg;
//
//    				caseWhen = createCaseWhen(cond, then);
//    				caseExpr = createCaseExpr(NULL, singleton(caseWhen), els);
//        		}

        		// ig attributes from shared
        		if(searchListNode(commonAttrNamesR, (Node *) createConstString(igOrigNameInteg)) ||
        				searchListNode(joinAttrNamesR, (Node *) createConstString(igOrigNameInteg)))
        		{
        			AttributeReference *corrIgExpr =
        					(AttributeReference *) MAP_GET_STRING(nameToIgAttrOpp, igOrigNameInteg);

    				cond = (Node *) createIsNullExpr((Node *) origIgInteg);
    				then = (Node *) corrIgExpr;
    				els = (Node *) origIgInteg;

    				caseWhen = createCaseWhen(cond, then);
    				caseExpr = createCaseExpr(NULL, singleton(caseWhen), els);
        		}
        		// either ig attributes from owned or non-common attributes
        		else
        		{
    				cond = (Node *) createIsNullExpr((Node *) origIgInteg);
    				then = (Node *) createCastExpr((Node *) createConstInt(0), DT_BIT10);
    				els = (Node *) origIgInteg;

    				caseWhen = createCaseWhen(cond, then);
    				caseExpr = createCaseExpr(NULL, singleton(caseWhen), els);
        		}

				newProjExprs = appendToTailOfList(newProjExprs,caseExpr);
        	}
    	}
    	else
        	newProjExprs = appendToTailOfList(newProjExprs,n);

    	pos++;
    }

    // replace project exprs with new project exprs
    newProj->projExprs = newProjExprs;
    INFO_OP_LOG("Rewritten tree having provenance attributes", newProj);


//    ProjectionOperator *hamming_op = createProjectionOp(newProjExprs,
//    		NULL, NIL, getAttrNames(newProj->op.schema));
//    addChildOperator((QueryOperator *) hamming_op, (QueryOperator *) newProj);
//	switchSubtrees((QueryOperator *) newProj, (QueryOperator *) hamming_op);


//    // Creating the HASH MAPS
//    List *newProjExpr = NIL;
//    int lenL = LIST_LENGTH(attrL) - 1;
//    int l = 0;
//    int posOfIgL = LIST_LENGTH(attrL) / 2;
//    int posOfIgR = LIST_LENGTH(attrR) / 2;
//
//    List *LprojExprs = NIL;
//    List *RprojExprs = NIL;
//    List* joinAttrs = NIL;
//
//    HashMap *nameToIgAttrNameL = NEW_MAP(Constant, Constant);
//    HashMap *nameToIgAttrNameR = NEW_MAP(Constant, Constant);
//
//
//
//    FOREACH(AttributeDef,a,attrL)
//    {
//		if(!isPrefix(a->attrName,"ig"))
//		{
//			char *key = a->attrName;
//			AttributeDef *igA = (AttributeDef *) getNthOfListP(attrL, posOfIgL);
//			char *value = igA->attrName;
//
//			ADD_TO_MAP(nameToIgAttrNameL,createStringKeyValue(key,value));
//			posOfIgL++;
//		}
//		else if(isSuffix(a->attrName,"anno"))
//		{
//			char *kv = a->attrName;
//			ADD_TO_MAP(nameToIgAttrNameL,createStringKeyValue(kv,kv));
//			posOfIgL++;
//		}
//    }
//
//    FOREACH(AttributeDef,a,attrR)
//	{
//		if(!isPrefix(a->attrName,"ig"))
//		{
//			char *key = a->attrName;
//			AttributeDef *igA = (AttributeDef *) getNthOfListP(attrR,posOfIgR);
//			char *value = igA->attrName;
//
//			ADD_TO_MAP(nameToIgAttrNameR,createStringKeyValue(key,value));
//			posOfIgR++;
//		}
//		else if(isSuffix(a->attrName,"anno"))
//		{
//			char *kv = a->attrName;
//			ADD_TO_MAP(nameToIgAttrNameR,createStringKeyValue(kv,kv));
//			posOfIgR++;
//		}
//	}
//
//
//    FOREACH(AttributeReference, n, newProj->projExprs)
//    {
//		if(l <= lenL)
//		{
//			LprojExprs = appendToTailOfList(LprojExprs, n);
//			l++;
//		}
//    }
//
//    l = 0;
//    FOREACH(AttributeReference, n, newProj->projExprs)
//    {
//		if(l > lenL)
//		{
//			RprojExprs = appendToTailOfList(RprojExprs, n);
//			l++;
//		}
//		else
//		{
//			l++;
//		}
//    }
//
//    int sizeLprojExprs = LIST_LENGTH(LprojExprs) - 1 / 2;
//    int cntLprojExprs = 0;
//	FOREACH(AttributeReference, n, LprojExprs)
//	{
//		if(!isPrefix(n->name, "ig") && !isSuffix(n->name, "anno") && cntLprojExprs < sizeLprojExprs)
//		{
//			newProjExpr = appendToTailOfList(newProjExpr, n);
//			cntLprojExprs = cntLprojExprs + 1;
//		}
//
//	}
//
//	cntLprojExprs = 0;
//	// creating case when statements here for integration
//	FOREACH(AttributeReference, n, LprojExprs)
//	{
//		if(!isPrefix(n->name, "ig") && !isSuffix(n->name, "anno") && !isA(n, CaseExpr))
//		{
//			if(MAP_HAS_STRING_KEY(nameToIgAttrNameR, n->name))
//			{
//				char *attrIgNameL = STRING_VALUE(MAP_GET_STRING(nameToIgAttrNameL, n->name));
//				char *attrIgNameR = STRING_VALUE(MAP_GET_STRING(nameToIgAttrNameR, n->name));
//
////				AttributeReference *ar = createFullAttrReference(attrIgNameL, 0,
////						listPosString(LattrNames,attrIgNameL), 0, DT_BIT10);
//
//				AttributeReference *ar = createFullAttrReference(attrIgNameL, 0,
//						getAttrPos((QueryOperator *) newProj, attrIgNameL), 0, DT_BIT10);
//
//				Node *cond = (Node *) createIsNullExpr((Node *) ar);
//
////				Node *then = (Node *) createFullAttrReference(attrIgNameR, 0,
////						LIST_LENGTH(LattrNames) + listPosString(RattrNames,attrIgNameR),
////						0, DT_BIT10);
//
//				Node *then = (Node *) createFullAttrReference(attrIgNameR, 0,
//						getAttrPos((QueryOperator *) newProj, attrIgNameR), 0, DT_BIT10);
//
//				Node *els = (Node *) ar;
//
//				CaseWhen *caseWhen = createCaseWhen(cond, then);
//				CaseExpr *caseExpr = createCaseExpr(NULL, singleton(caseWhen), els);
//
//				newProjExpr = appendToTailOfList(newProjExpr, caseExpr);
//				cntLprojExprs = cntLprojExprs + 1;
//			}
//			else
//			{
//				char *igAttr = STRING_VALUE(MAP_GET_STRING(nameToIgAttrNameL, n->name));
////				AttributeReference *ar = createFullAttrReference(igAttr, 0,
////						listPosString(LattrNames,igAttr), 0, DT_BIT10);
//
//				AttributeReference *ar = createFullAttrReference(igAttr, 0,
//						getAttrPos((QueryOperator *) newProj, igAttr), 0, DT_BIT10);
//
//
//				newProjExpr = appendToTailOfList(newProjExpr, ar);
//				cntLprojExprs = cntLprojExprs + 1;
//			}
//
//		}
//		// is this correct ? because there already is a case when statement so do we need the old ones ?
//		else if(isA(n, CaseExpr) && cntLprojExprs >= sizeLprojExprs)
//		{
//			newProjExpr = appendToTailOfList(newProjExpr, n);
//		}
//		else if(isSuffix(n->name, "anno"))
//		{
//			newProjExpr = appendToTailOfList(newProjExpr, n);
//		}
//
//	}
//
//
//    int sizeRprojExprs = LIST_LENGTH(RprojExprs) - 1 / 2;
//    int cntRprojExprs = 0;
//	FOREACH(AttributeReference, n, RprojExprs)
//	{
//		if(!isPrefix(n->name, "ig") && !isSuffix(n->name, "anno") && cntRprojExprs < sizeRprojExprs)
//		{
//			newProjExpr = appendToTailOfList(newProjExpr, n);
//			cntRprojExprs = cntRprojExprs + 1;
//		}
//
//	}
//
//	cntRprojExprs = 0;
//	FOREACH(AttributeReference, n, RprojExprs)
//	{
//		if(!isPrefix(n->name, "ig") && !isSuffix(n->name, "anno") && !isA(n, CaseExpr))
//		{
//			char *ch = replaceSubstr(n->name, "1", "");
//
//			if(MAP_HAS_STRING_KEY(nameToIgAttrNameL, ch))
//			{
//				char *attrIgNameL = STRING_VALUE(MAP_GET_STRING(nameToIgAttrNameL, ch));
//				char *attrIgNameR = STRING_VALUE(MAP_GET_STRING(nameToIgAttrNameR, ch));
//
////				AttributeReference *ar = createFullAttrReference(attrIgNameR, 0,
////						LIST_LENGTH(LattrNames) + listPosString(RattrNames,attrIgNameR),
////						0, DT_BIT10);
//
//				AttributeReference *ar = createFullAttrReference(attrIgNameR, 0,
//						getAttrPos((QueryOperator *) newProj, attrIgNameR), 0, DT_BIT10);
//
//				Node *cond = (Node *) createIsNullExpr((Node *) ar);
//
////				Node *then = (Node *) createFullAttrReference(attrIgNameL, 0,
////						listPosString(LattrNames,attrIgNameL), 0, DT_BIT10);
////
//
//				Node *then = (Node *) createFullAttrReference(attrIgNameL, 0,
//						getAttrPos((QueryOperator *) newProj, attrIgNameL), 0, DT_BIT10);
//
//				Node *els  = (Node *) ar;
//
//				CaseWhen *caseWhen = createCaseWhen(cond, then);
//				CaseExpr *caseExpr = createCaseExpr(NULL, singleton(caseWhen), els);
//
//				newProjExpr = appendToTailOfList(newProjExpr, caseExpr);
//				cntRprojExprs = cntRprojExprs + 1;
//			}
//			else
//			{
//				char *igAttr = STRING_VALUE(MAP_GET_STRING(nameToIgAttrNameR, ch));
////				AttributeReference *ar = createFullAttrReference(igAttr, 0,
////										 listPosString(RattrNames,igAttr) + lenL + 1, 0, DT_BIT10);
//
//				AttributeReference *ar = createFullAttrReference(igAttr, 0,
//						getAttrPos((QueryOperator *) newProj, igAttr), 0, DT_BIT10);
//
//				newProjExpr = appendToTailOfList(newProjExpr, ar);
//				cntRprojExprs = cntRprojExprs + 1;
//			}
//		}
//		else if(isA(n, CaseExpr) && cntRprojExprs >= sizeRprojExprs)
//		{
//			newProjExpr = appendToTailOfList(newProjExpr, n);
//		}
//		else if(isSuffix(n->name, "anno"))
//		{
//			newProjExpr = appendToTailOfList(newProjExpr, n);
//		}
//	}
//
//
////	List *attrNames = CONCAT_LISTS(LattrNames,RattrNames);
////	newProj
//	List *attrNames = NIL;
//    List *LattrDefs = NIL;
//    List *RattrDefs = NIL;
//    int len = LIST_LENGTH(newProj->op.schema->attrDefs);
//    int c = 0;
//
//	FOREACH(AttributeDef, a, newProj->op.schema->attrDefs)
//	{
//		attrNames = appendToTailOfList(attrNames, a->attrName);
//
//		if(c < len/2)
//		{
//			LattrDefs = appendToTailOfList(LattrDefs, a);
//			c ++;
//		}
//		else
//		{
//			RattrDefs = appendToTailOfList(RattrDefs, a);
//			c++;
//		}
//
//	}
//
//
//    ProjectionOperator *op1 = createProjectionOp(newProjExpr, NULL, NIL, attrNames);
//    op1->op.schema->attrDefs = newProj->op.schema->attrDefs;
//
//    addChildOperator((QueryOperator *) op1, (QueryOperator *) newProj);
//    switchSubtrees((QueryOperator *) newProj, (QueryOperator *) op1);
//
//
//
    // Adding hammingDist function
    List *exprs = NIL;
    List *atNames = NIL;
    int x = 0;

    FOREACH(AttributeDef, a, newProj->op.schema->attrDefs)
	{
    	if(isPrefix(a->attrName, IG_PREFIX))
    	{
    		AttributeReference *ar = createFullAttrReference(a->attrName, 0, x, 0, DT_BIT10);
			exprs = appendToTailOfList(exprs, ar);
			atNames = appendToTailOfList(atNames, a->attrName);
    	}
    	else
    	{
    		AttributeReference *ar = createFullAttrReference(a->attrName, 0, x, 0, a->dataType);
			exprs = appendToTailOfList(exprs, ar);
			atNames = appendToTailOfList(atNames, a->attrName);
    	}

    	x++;
	}

//	// for the join attributes
//	List *functioninput = NIL;
//	char *tempName = NULL;
//	List *joinAttrs = (List *) GET_STRING_PROP(newProj, PROP_JOIN_ATTRS_FOR_HAMMING);
//	int cnt = 0;
//
//	FOREACH(AttributeReference, n, joinAttrs)
//	{
//		//GETS THE JOIN ATTRIBUTE FROM FIRST TABLE
//		if(n->fromClauseItem == 0)
//		{
//			if(MAP_HAS_STRING_KEY(nameToIgAttrName, n->name))
//			{
//				char *attrName = STRING_VALUE(MAP_GET_STRING(nameToIgAttrName, n->name));
////				AttributeReference *ar = createFullAttrReference(attrName, 0,
////										listPosString(LattrNames,attrName), 0,
////										isPrefix(attrName,"ig") ? DT_BIT10 : n->attrType);
//
//
//				AttributeReference *ar = createFullAttrReference(attrName, 0,
//										getAttrPos((QueryOperator *) newProj, attrName), 0,
//										isPrefix(attrName,"ig_") ? DT_BIT10 : n->attrType);
//
//
//				CastExpr *castL;
//				castL = createCastExpr((Node *) ar, DT_STRING);
//				functioninput = appendToTailOfList(functioninput, castL);
//				tempName = n->name;
//				cnt ++;
//			}
//		}
//
//		//GETS THE JOIN ATTRIBUTE FROM SECOND TABLE
//		if(n->fromClauseItem == 1)
//		{
//			if(MAP_HAS_STRING_KEY(nameToIgAttrName, n->name))
//			{
//				char *attrName = STRING_VALUE(MAP_GET_STRING(nameToIgAttrName, n->name));
////				AttributeReference *ar = createFullAttrReference(attrName, 0,
////						LIST_LENGTH(LattrNames) + listPosString(RattrNames,attrName) - (lenL + 1),
////						0, isPrefix(attrName,"ig") ? DT_BIT10 : n->attrType);
//
//				AttributeReference *ar = createFullAttrReference(attrName, 0,
//										getAttrPos((QueryOperator *) newProj, attrName),
//										0, isPrefix(attrName,"ig") ? DT_BIT10 : n->attrType);
//
//				CastExpr *castR;
//				castR = createCastExpr((Node *) ar, DT_STRING);
//				functioninput = appendToTailOfList(functioninput, castR);
//				cnt ++;
//			}
//		}
//
//		if(cnt == 2)
//		{
//			atNames = appendToTailOfList(atNames, CONCAT_STRINGS("hamming_", tempName));
//			FunctionCall *hammingdist = createFunctionCall("hammingdist", functioninput);
//			exprs = appendToTailOfList(exprs,hammingdist);
//			functioninput = NIL;
//			cnt = 0;
//		}
//
//	}
//
//	List *joinNames = NIL;
//	FOREACH(AttributeReference, n, joinAttrs)
//	{
//		joinNames = appendToTailOfList(joinNames, n->name);
//	}

//    List *exprs = getAttrReferences((Node *) newProj->projExprs);
//    List *attrNames = getAttrNames(newProj->op.schema);

//	FOREACH(AttributeReference, n, LprojExprs)
	FOREACH(AttributeDef, n, newProj->op.schema->attrDefs)
	{
		List *functioninput = NIL;
		List *cast = NIL;

//		boolean flag = searchListString(joinNames, n->attrName);

		if(isPrefix(n->attrName, IG_PREFIX) && isSuffix(n->attrName, INTEG_SUFFIX))
//				flag == FALSE)
		{
			char *origNameOfInteg = replaceSubstr(n->attrName,INTEG_SUFFIX,"");

			if(MAP_HAS_STRING_KEY(nameToIgAttrRef, origNameOfInteg))
//					&& !isSuffix(n->attrName, "anno"))
			{
//				char *attrIgNameL = STRING_VALUE(MAP_GET_STRING(nameToIgAttrRef, n->attrName));

				AttributeReference *attrIgL = getAttrRefByName((QueryOperator *) newProj, n->attrName);

//				AttributeReference *tempIgR = (AttributeReference *) MAP_GET_STRING(nameToIgAttrRef, origNameOfInteg);
				AttributeReference *attrIgR = getAttrRefByName((QueryOperator *) newProj, origNameOfInteg);

//				AttributeReference *arL = createFullAttrReference(attrIgNameL, 0,
//						listPosString(LattrNames,attrIgNameL), 0,
//						isPrefix(attrIgNameL,"ig") ? DT_BIT10 : n->attrType);

//				AttributeReference *arL = createFullAttrReference(attrIgNameL, 0,
//						getAttrPos((QueryOperator *) newProj, attrIgNameL), 0,
//						isPrefix(attrIgNameL,"ig_") ? DT_BIT10 : DT_INT);

//				AttributeReference *arL = getAttrRefByName((QueryOperator *) newProj, attrIgNameL);

//				AttributeReference *arR = createFullAttrReference(attrIgNameR, 0,
//						LIST_LENGTH(LattrNames) + listPosString(RattrNames,attrIgNameR) - (lenL + 1),
//						0, isPrefix(attrIgNameR,"ig") ? DT_BIT10 : n->attrType);


//				AttributeReference *arR = createFullAttrReference(attrIgNameR, 0,
//						getAttrPos((QueryOperator *) newProj, attrIgNameR), 0,
//						isPrefix(attrIgNameR,"ig_") ? DT_BIT10 : DT_INT);

//				AttributeReference *arR = getAttrRefByName((QueryOperator *) newProj, attrIgNameR);

				CastExpr *castL;
				CastExpr *castR;

				castL = createCastExpr((Node *) attrIgL, DT_STRING);
				castR = createCastExpr((Node *) attrIgR, DT_STRING);

				cast = appendToTailOfList(cast, castL);
				cast = appendToTailOfList(cast, castR);

				functioninput = appendToTailOfList(functioninput, attrIgL);
				functioninput = appendToTailOfList(functioninput, attrIgR);

				FunctionCall *hammingdist = createFunctionCall("hammingdist", cast);
				Node *cond = (Node *)(createOpExpr("=",functioninput));
				Node *then = (Node *)(createConstString("0000000000"));
				Node *els  = (Node *) hammingdist;

				CaseWhen *caseWhen = createCaseWhen(cond, then);
				CaseExpr *caseExpr = createCaseExpr(NULL, singleton(caseWhen), els);

				exprs = appendToTailOfList(exprs,caseExpr);
				atNames = appendToTailOfList(atNames, CONCAT_STRINGS(HAMMING_PREFIX, n->attrName));
//				x++;
			}

//			else if(!MAP_HAS_STRING_KEY(nameToIgAttrName, n->attrName) && !isSuffix(n->attrName, "anno"))
//			{
//				char *attrIgNameL = STRING_VALUE(MAP_GET_STRING(nameToIgAttrName, n->attrName));
//
////				AttributeReference *arL = createFullAttrReference(attrIgNameL, 0,
////										listPosString(LattrNames,attrIgNameL), 0,
////										isPrefix(attrIgNameL,"ig") ? DT_BIT10 : n->attrType);
//
//				AttributeReference *arL = createFullAttrReference(attrIgNameL, 0,
//										getAttrPos((QueryOperator *) newProj, attrIgNameL), 0,
//										isPrefix(attrIgNameL,"ig") ? DT_BIT10 :DT_INT);
//
////				AttributeReference *arL = getAttrRefByName((QueryOperator *) newProj, attrIgNameL);
//
//				CastExpr *castL;
//
//				castL = createCastExpr((Node *) arL, DT_STRING);
//
//				functioninput = appendToTailOfList(functioninput, castL);
//				functioninput = appendToTailOfList(functioninput, createConstString("000000000000000"));
//				FunctionCall *hammingdist = createFunctionCall("hammingdist", functioninput);
//
//				exprs = appendToTailOfList(exprs,hammingdist);
//				atNames = appendToTailOfList(atNames, CONCAT_STRINGS("hamming_", n->attrName));
//				x++;
//			}
		}
	}

////	FOREACH(AttributeReference, n, RprojExprs)
//	FOREACH(AttributeDef, n, RattrDefs)
//	{
//		List *functioninput = NIL;
//		boolean flag = searchListString(joinNames, n->attrName);
//		if(!isPrefix(n->attrName, "ig") && flag == FALSE)
//		{
//			char *ch = replaceSubstr(n->attrName, "1", "");
//			if(MAP_HAS_STRING_KEY(nameToIgAttrNameL, ch) && !isSuffix(n->attrName, "anno") )
//			{
//				x++;
//				continue;
//			}
//			else if(!MAP_HAS_STRING_KEY(nameToIgAttrNameL, ch) && !isSuffix(n->attrName, "anno"))
//			{
//				char *attrIgNameR = STRING_VALUE(MAP_GET_STRING(nameToIgAttrNameR, ch));
//
////				AttributeReference *arR = createFullAttrReference(attrIgNameR, 0,
////										LIST_LENGTH(LattrNames) + listPosString(RattrNames,attrIgNameR) - (lenL + 1),
////										0, isPrefix(attrIgNameR,"ig") ? DT_BIT10 : n->attrType);
//
//				AttributeReference *arR = createFullAttrReference(attrIgNameR, 0,
//										getAttrPos((QueryOperator *) newProj, attrIgNameR),
//										0, isPrefix(attrIgNameR,"ig") ? DT_BIT10 : DT_INT);
//
////				AttributeReference *arR = getAttrRefByName((QueryOperator *) newProj, attrIgNameR);
//
//				CastExpr *castR;
//				castR = createCastExpr((Node *) arR, DT_STRING);
//
//				functioninput = appendToTailOfList(functioninput, castR);
//				functioninput = appendToTailOfList(functioninput, createConstString("000000000000000"));
//				FunctionCall *hammingdist = createFunctionCall("hammingdist", functioninput);
//
//				exprs = appendToTailOfList(exprs,hammingdist);
//				atNames = appendToTailOfList(atNames, CONCAT_STRINGS("hamming_", n->attrName));
//				x++;
//			}
//		}
//	}

	ProjectionOperator *hamming_op = createProjectionOp(exprs, NULL, NIL, atNames);

	FOREACH(AttributeDef, n, hamming_op->op.schema->attrDefs)
	{
		if(isPrefix(n->attrName, HAMMING_PREFIX))
		{
			n->dataType = DT_STRING;
		}
	}

	FOREACH(AttributeReference, n, hamming_op->projExprs)
	{
		if(isPrefix(n->name, HAMMING_PREFIX))
		{
			n->attrType = DT_STRING;
		}
	}

	FOREACH(AttributeReference, n, hamming_op->projExprs)
	{
		if(isA(n, FunctionCall))
		{
			FunctionCall *x = (FunctionCall *) n;
			x->isDistinct = FALSE;

		}
	}

    addChildOperator((QueryOperator *) hamming_op, (QueryOperator *) newProj);
    switchSubtrees((QueryOperator *) newProj, (QueryOperator *) hamming_op);
    INFO_OP_LOG("Rewritten tree for hamming distance", hamming_op);

    if(HAS_STRING_PROP(newProj, IG_PROP_ORIG_ATTR))
	{
		SET_STRING_PROP(hamming_op, IG_PROP_ORIG_ATTR,
				copyObject(GET_STRING_PROP(newProj, IG_PROP_ORIG_ATTR)));
	}

//    SET_BOOL_STRING_PROP(hamming_op, PROP_MATERIALIZE);


//    //Adding a projection to display _hamming attributes
//    List *hammingProj = NIL;
//    int posP = 0;
//	FOREACH(AttributeDef, a, hamming_op->op.schema->attrDefs)
//	{
//		AttributeReference *ar = createFullAttrReference(a->attrName, 0, posP,0, a->dataType);
//		hammingProj = appendToTailOfList(hammingProj, ar);
//	}
//
//	ProjectionOperator *hamming_op1 = createProjectionOp(hammingProj, NULL, NIL, atNames);
//	addChildOperator((QueryOperator *) hamming_op1, (QueryOperator *) hamming_op);
//	switchSubtrees((QueryOperator *) hamming_op, (QueryOperator *) hamming_op1);



    //Adding hammingdistvalue function
	List *h_valueExprs = NIL;
	List *h_valueName = NIL;
	int posV = 0;

	FOREACH(AttributeDef, a, hamming_op->op.schema->attrDefs)
	{
		if(isPrefix(a->attrName, HAMMING_PREFIX))
		{
			AttributeReference *ar = createFullAttrReference(a->attrName, 0, posV,0, a->dataType);
			h_valueExprs = appendToTailOfList(h_valueExprs, ar);
			h_valueName = appendToTailOfList(h_valueName, a->attrName);
		}
		else
		{
			AttributeReference *ar = createFullAttrReference(a->attrName, 0, posV,0, a->dataType);
			h_valueExprs = appendToTailOfList(h_valueExprs, ar);
			h_valueName = appendToTailOfList(h_valueName, a->attrName);
		}

		posV++;
	}

	posV = 0;
	List *newExprs = copyObject(h_valueExprs);

	FOREACH(AttributeReference, a, newExprs)
	{
		if(isPrefix(a->name, HAMMING_PREFIX))
		{
//			AttributeReference *ar = createFullAttrReference(a->name, 0, posV,0, a->attrType);
			FunctionCall *hammingdistvalue = createFunctionCall("hammingdistvalue", singleton(a));

			h_valueExprs = appendToTailOfList(h_valueExprs, hammingdistvalue);
			h_valueName = appendToTailOfList(h_valueName, CONCAT_STRINGS(VALUE_IG, a->name));
		}

		posV++;
	}

//	h_valueExprs = CONCAT_LISTS(h_valueExprs, oldExprs);
//	h_valueName = CONCAT_LISTS(h_valueName, oldNames);

	ProjectionOperator *hammingvalue_op = createProjectionOp(h_valueExprs, NULL, NIL, h_valueName);

	FOREACH(AttributeDef, n, hammingvalue_op->op.schema->attrDefs)
	{
		if(isPrefix(n->attrName, VALUE_IG))
		{
			n->dataType = DT_INT;
		}
	}

	FOREACH(AttributeReference, n, hammingvalue_op->projExprs)
	{
		if(isPrefix(n->name, VALUE_IG))
		{
			n->attrType = DT_INT;
		}
	}

	addChildOperator((QueryOperator *) hammingvalue_op, (QueryOperator *) hamming_op);
	switchSubtrees((QueryOperator *) hamming_op, (QueryOperator *) hammingvalue_op);

    if(HAS_STRING_PROP(hamming_op, IG_PROP_ORIG_ATTR))
	{
		SET_STRING_PROP(hammingvalue_op, IG_PROP_ORIG_ATTR,
				copyObject(GET_STRING_PROP(hamming_op, IG_PROP_ORIG_ATTR)));
	}

	return hammingvalue_op;
}


static AggregationOperator *
rewriteIG_PatternGeneration (ProjectionOperator *sumrows)
{

	ASSERT(OP_LCHILD(sumrows));
	DEBUG_LOG("REWRITE-IG - Pattern Generation");
	DEBUG_LOG("Operator tree \n%s", nodeToString(sumrows));


	int lenL = (LIST_LENGTH(attrL) - 1) / 2;
	int lenR = (LIST_LENGTH(attrR) - 1) / 2;
	int cntR = 0;
	int cntL = 0;
	List *Laggrs = NIL;;
	List *Raggrs = NIL;
	List *LaggrsNames = NIL;
	List *RaggrsNames = NIL;

	FOREACH(AttributeDef, n, attrL)
	{

		if(cntL < lenL)
//		if(!isPrefix(n->attrName,IG_PREFIX) && !isSuffix(n->attrName,"_anno"))
		{
			Laggrs = appendToTailOfList(Laggrs, n);
			LaggrsNames = appendToTailOfList(LaggrsNames, n->attrName);
			cntL = cntL + 1;
		}
	}

	FOREACH(AttributeDef, n, attrR)
	{

		if(cntR < lenR)
//		if(!isPrefix(n->attrName,IG_PREFIX) && !isSuffix(n->attrName,"_anno"))
		{
			Raggrs = appendToTailOfList(Raggrs, n);
			RaggrsNames = appendToTailOfList(RaggrsNames, n->attrName);
			cntR = cntR + 1;
		}
	}


	List *cleanExprs = NIL;
	List *cleanNames = NIL;

	//Creating Left Case when statements
	FOREACH(AttributeDef, L, Laggrs)
	{

		if(searchListString(RaggrsNames, L->attrName))
		{
			FOREACH(AttributeDef, R, Raggrs)
			{
//				List *functioninput = NIL;
				char *LAttrName = L->attrName;

				if(streq(L->attrName, R->attrName))
				{
					AttributeReference * arL = createFullAttrReference(LAttrName, 0,
							getAttrPos((QueryOperator *) sumrows, LAttrName),0, L->dataType);

					//TODO: search attributes from shared
					if(arL->attrPosition == -1)
					{
						LAttrName = CONCAT_STRINGS(L->attrName,gprom_itoa(1));
						arL->name = LAttrName;
						arL->attrPosition = getAttrPos((QueryOperator *) sumrows, LAttrName);
					}

//					AttributeReference * arR = createFullAttrReference(R->attrName, 0,
//							getAttrPos((QueryOperator *) sumrows, L->attrName),0, R->dataType);

//					functioninput = appendToTailOfList(functioninput, arL);
//					functioninput = appendToTailOfList(functioninput, arR);
//					Node *cond = (Node *)(createOpExpr("=",functioninput));
//
//					Node *then = (Node *) arL;
//
//					CaseWhen *caseWhen = createCaseWhen(cond, then);
//
//					CaseExpr *caseExpr = createCaseExpr(NULL, singleton(caseWhen), NULL);

					cleanExprs = appendToTailOfList(cleanExprs, arL);
					cleanNames = appendToTailOfList(cleanNames, CONCAT_STRINGS(INDEX, LAttrName));

				}

			}
		}
		else
		{
			AttributeReference * arL = createFullAttrReference(L->attrName, 0,
					getAttrPos((QueryOperator *) sumrows, L->attrName),0, L->dataType);
			cleanExprs = appendToTailOfList(cleanExprs, arL);
			cleanNames = appendToTailOfList(cleanNames, CONCAT_STRINGS(INDEX, L->attrName));
		}
	}


	FOREACH(AttributeDef, R, Raggrs)
	{
		if(!searchListString(LaggrsNames, R->attrName))
		{
			AttributeReference * arR = createFullAttrReference(R->attrName, 0,
					getAttrPos((QueryOperator *) sumrows, R->attrName),0, R->dataType);

			cleanExprs = appendToTailOfList(cleanExprs, arR);
			cleanNames = appendToTailOfList(cleanNames, CONCAT_STRINGS(INDEX, R->attrName));

		}
	}



//	//TODO: how to handle arithmetic operator
//	FOREACH(Node, n, sumrows->projExprs)
//	{
//		if(isA(n,AttributeReference))
//		{
//			AttributeReference *ar = (AttributeReference *) n;
//
//			if(!isPrefix(ar->name,IG_PREFIX) &&
//					!isPrefix(ar->name,HAMMING_PREFIX) &&
//						!isPrefix(ar->name,VALUE_IG))
//			{
//				cleanExprs = appendToTailOfList(cleanExprs,n);
//				cleanNames = appendToTailOfList(cleanNames, ar->name);
//			}
//		}
//	}

	// add ig columns and rowIG
	FOREACH(AttributeReference, n, sumrows->projExprs)
	{
		if(isPrefix(n->name,VALUE_IG))
		{
			cleanExprs = appendToTailOfList(cleanExprs,n);
			cleanNames = appendToTailOfList(cleanNames, n->name);
		}
	}

	FOREACH(AttributeDef, a, sumrows->op.schema->attrDefs)
	{
		if(streq(a->attrName,TOTAL_DIST))
		{
			AttributeReference *ar = createFullAttrReference(a->attrName, 0,
					getAttrPos((QueryOperator *) sumrows, a->attrName), 0, a->dataType);

			cleanExprs = appendToTailOfList(cleanExprs,ar);
			cleanNames = appendToTailOfList(cleanNames, ar->name);
		}
	}

	ProjectionOperator *clean = createProjectionOp(cleanExprs, NULL, NIL, cleanNames);
	addChildOperator((QueryOperator *) clean, (QueryOperator *) sumrows);
	switchSubtrees((QueryOperator *) sumrows, (QueryOperator *) clean);


	List *projNames = NIL;
	List *groupBy = NIL;
	List *aggrs = NIL;
	FunctionCall *sum = NULL;

	projNames = appendToTailOfList(projNames, strdup(PATTERN_IG));
	FOREACH(AttributeDef, n, clean->op.schema->attrDefs)
	{
		if(isPrefix(n->attrName, strdup(INDEX)))
		{
			groupBy = appendToTailOfList(groupBy,
					  createFullAttrReference(n->attrName, 0,
					  getAttrPos((QueryOperator *) clean, n->attrName), 0, n->dataType));

			projNames = appendToTailOfList(projNames, n->attrName);

		}

		//this one makes pattern_IG
		if(streq(n->attrName, TOTAL_DIST))
		{
			AttributeReference *ar = createFullAttrReference(n->attrName, 0,
					   				 getAttrPos((QueryOperator *) clean, n->attrName), 0, n->dataType);
			sum = createFunctionCall("SUM", singleton(ar));
			aggrs = appendToTailOfList(aggrs,sum);

		}
	}

	AggregationOperator *ao = createAggregationOp(aggrs, groupBy, NULL, NIL, projNames);
	ao->isCube = TRUE;
	FOREACH(AttributeDef, n, ao->op.schema->attrDefs)
	{
		if(isPrefix(n->attrName, strdup(PATTERN_IG)))
		{
			n->dataType = DT_INT;
			break;
		}

	}
	addChildOperator((QueryOperator *) ao, (QueryOperator *) clean);
	switchSubtrees((QueryOperator *) clean, (QueryOperator *) ao);

	// Adding projection for Informativeness
	List *informExprs = NIL;
	List *informNames = NIL;

	int pos = 0;

	FOREACH(AttributeDef, n, ao->op.schema->attrDefs)
	{
		if(isPrefix(n->attrName, INDEX))
		{
			informExprs = appendToTailOfList(informExprs,
					  createFullAttrReference(n->attrName, 0,
							  pos, 0, n->dataType));
			informNames = appendToTailOfList(informNames, n->attrName);
		}

		pos = pos + 1;
	}

	pos = 0;

	FOREACH(AttributeDef, n, ao->op.schema->attrDefs)
	{
		if(isPrefix(n->attrName, "pattern"))
		{
			// Adding patern_IG in the new informProj
			informExprs = appendToTailOfList(informExprs,
						  createFullAttrReference(n->attrName, 0,
						  0, 0, DT_INT));
			informNames = appendToTailOfList(informNames, n->attrName);
		}

		pos++;
	}


	// ADDING INFORMATIVENESS
	pos = 1;
	List *sumExprs = NIL;
	Node *sumExpr = NULL;

	FOREACH(AttributeDef, n , ao->op.schema->attrDefs)
	{
		if(isPrefix(n->attrName, INDEX))
		{

			AttributeReference *ar = createFullAttrReference(n->attrName, 0, pos, 0, n->dataType);
			pos = pos + 1;

			Node *cond = (Node *) createOpExpr(OPNAME_NOT, singleton(createIsNullExpr((Node *) ar)));
			Node *then = (Node *) (createConstInt(1));
			Node *els = (Node *) (createConstInt(0));


			CaseWhen *caseWhen = createCaseWhen(cond, then);
			CaseExpr *caseExpr = createCaseExpr(NULL, singleton(caseWhen), els);

			sumExprs = appendToTailOfList(sumExprs, caseExpr);

		}

	}

	sumExpr = (Node *) (createOpExpr("+", sumExprs));
	informExprs = appendToTailOfList(informExprs, sumExpr);
	informNames = appendToTailOfList(informNames, strdup(INFORMATIVENESS));

	// ADDING COVERAGE
	pos = 1;
	int num_i = 0;
	// counting attributes
	FOREACH(AttributeDef, n, ao->op.schema->attrDefs)
	{
		if(isPrefix(n->attrName, INDEX))
		{
			num_i = num_i + 1;
		}

	}

	Constant *countProv = createConstInt(1);
	FunctionCall *count = createFunctionCall("COUNT", singleton(countProv));
	informExprs = appendToTailOfList(informExprs, count);
	informNames = appendToTailOfList(informNames, strdup(COVERAGE));


	ProjectionOperator *inform = createProjectionOp(informExprs, NULL, NIL, informNames);
	addChildOperator((QueryOperator *) inform, (QueryOperator *) ao);
	switchSubtrees((QueryOperator *) ao, (QueryOperator *) inform);

	SET_BOOL_STRING_PROP(inform, PROP_MATERIALIZE);
	DEBUG_NODE_BEATIFY_LOG("Generate Patterns While Computing Informativeness and Coverage: ", inform);

//	// TODO: fix coverage datatype
//	FOREACH(AttributeDef, a, inform->op.schema->attrDefs)
//		if(streq(a->attrName, COVERAGE))
//			a->dataType = DT_INT;


//	List *soNames = NIL;
//	AttributeReference *cov = NULL;
//	AttributeReference *inf = NULL;
//
//	FOREACH(AttributeDef, n, inform->op.schema->attrDefs)
//	{
//		soNames = appendToTailOfList(soNames, n->attrName);
//
//		if(streq(n->attrName,"coverage"))
//		{
//			cov = createFullAttrReference(n->attrName, 0,
//					getAttrPos((QueryOperator *) inform, n->attrName), 0, n->dataType);
//		}
//
//		if(streq(n->attrName,"informativeness"))
//		{
//			inf = createFullAttrReference(n->attrName, 0,
//					getAttrPos((QueryOperator *) inform, n->attrName), 0, n->dataType);
//		}
//	}
//
////	QueryOperator *so = (QueryOperator *) inform;
//
//	//creating where condition coverage > 1
//	Node *whereClauseL = (Node *) createOpExpr(OPNAME_GT, LIST_MAKE(cov, createConstInt(1)));
//	SelectionOperator *soL = createSelectionOp(whereClauseL, (QueryOperator *) inform, NIL, soNames);
//	addParent((QueryOperator *) inform, (QueryOperator *) soL);
//
//	//creating where condition coverage = 1 AND informativeness = 5
//	Node *cov1 = (Node *) createOpExpr(OPNAME_EQ, LIST_MAKE(cov, createConstInt(1)));
//	Node *info5 = (Node *) createOpExpr(OPNAME_EQ, LIST_MAKE(inf, createConstInt(num_i)));
//	Node *whereClauseR = (Node *) createOpExpr(OPNAME_AND, LIST_MAKE(cov1,info5));
////						//this is to create coverage = 1
////						createOpExpr(OPNAME_EQ, LIST_MAKE(cov, createConstInt(1))),
////						// this is to make informativeness = 5
////						createOpExpr(OPNAME_EQ, LIST_MAKE(inf, createConstInt(num_i)))));
//
//	SelectionOperator *soR = createSelectionOp(whereClauseR, (QueryOperator *) inform, NIL, soNames);
//	addParent((QueryOperator *) inform, (QueryOperator *) soR);
//
//	// create union operator
//	List *soLR = LIST_MAKE(soL, soR);
//	SetOperator *unionOp = createSetOperator(SETOP_UNION, soLR, NIL, informNames);
//
//	OP_LCHILD(unionOp)->parents = OP_RCHILD(unionOp)->parents = singleton(unionOp);
////	QueryOperator *result = (QueryOperator *) unionOp;
//
////	addChildOperator((QueryOperator *) unionOp, (QueryOperator *) inform);
////	switchSubtrees((QueryOperator *) soL, unionOp);
//
//	List *removeNoGoodPatt = NIL;
//	List *removeNoGoodPattNames = NIL;
//
//	FOREACH(AttributeReference, n, inform->projExprs)
//	{
//		removeNoGoodPatt = appendToTailOfList(removeNoGoodPatt, n);
//	}
//
//	FOREACH(AttributeDef, n, inform->op.schema->attrDefs)
//	{
//		removeNoGoodPattNames = appendToTailOfList(removeNoGoodPattNames, n->attrName);
//	}
//
//	ProjectionOperator *projUnion = createProjectionOp(removeNoGoodPatt,
//			(QueryOperator *) unionOp, NIL, removeNoGoodPattNames);
////	addChildOperator((QueryOperator *) projUnion, (QueryOperator *) unionOp);
//	switchSubtrees((QueryOperator *) unionOp, (QueryOperator *) projUnion);


	// remove no good patterns
//	List *soNames = NIL;
	AttributeReference *cov = getAttrRefByName((QueryOperator *) inform, COVERAGE);
	AttributeReference *inf = getAttrRefByName((QueryOperator *) inform, INFORMATIVENESS);

//	FOREACH(AttributeDef, n, inform->op.schema->attrDefs)
//	{
////		soNames = appendToTailOfList(soNames, n->attrName);
//
//		if(streq(n->attrName,"coverage"))
//		{
//			cov = createFullAttrReference(n->attrName, 0,
//					getAttrPos((QueryOperator *) inform, n->attrName), 0, n->dataType);
//		}
//
//		if(streq(n->attrName,"informativeness"))
//		{
//			inf = createFullAttrReference(n->attrName, 0,
//					getAttrPos((QueryOperator *) inform, n->attrName), 0, n->dataType);
//		}
//	}

	//creating where condition coverage > 1 OR (coverage = 1 AND informativeness = 5)
	Node *covgt1 = (Node *) createOpExpr(OPNAME_GT, LIST_MAKE(cov, createConstInt(1)));
	Node *cov1 = (Node *) createOpExpr(OPNAME_EQ, LIST_MAKE(cov, createConstInt(1)));
	Node *info5 = (Node *) createOpExpr(OPNAME_EQ, LIST_MAKE(inf, createConstInt(num_i)));

	Node *subcond = (Node *) createOpExpr(OPNAME_AND, LIST_MAKE(cov1,info5));
	Node *cond = (Node *) createOpExpr(OPNAME_OR, LIST_MAKE(covgt1,subcond));

	SelectionOperator *so = createSelectionOp(cond, NULL, NIL, getAttrNames(inform->op.schema));
	addChildOperator((QueryOperator *) so, (QueryOperator *) inform);
	switchSubtrees((QueryOperator *) inform, (QueryOperator *) so);

//	SET_BOOL_STRING_PROP(so, PROP_MATERIALIZE);

	// TODO: fix datatype
	FORBOTH(AttributeDef, al, ar, so->op.schema->attrDefs, inform->op.schema->attrDefs)
		if(al->dataType != ar->dataType)
			al->dataType = ar->dataType;

	DEBUG_NODE_BEATIFY_LOG("Remove No Good Patterns: ", so);

//	// TODO: fix coverage datatype
//	FOREACH(AttributeDef, a, so->op.schema->attrDefs)
//		if(streq(a->attrName, COVERAGE))
//			a->dataType = DT_INT;


//	List *LJoinAttrs = NIL;
//	List *RJoinAttrs = NIL;
	List *JoinAttrNames = NIL;
	List *joinList = NIL;
	Node *joinCondt = NULL;

//	// getting all the patterns from removeNoGoodPatt OR so L
//	FOREACH(AttributeDef, n, so->op.schema->attrDefs)
//	{
////		AttributeReference *ar = createFullAttrReference(n->attrName, 0,
////								 getAttrPos((QueryOperator *) inform, n->attrName), 0, n->dataType);
////		LJoinAttrs = appendToTailOfList(LJoinAttrs, ar);
//		JoinAttrNames = appendToTailOfList(JoinAttrNames, n->attrName);
//	}
//
//	//getting all the data from rowIG OR clean R
//	FOREACH(AttributeDef, n, clean->op.schema->attrDefs)
//	{
////		AttributeReference *ar = createFullAttrReference(n->attrName, 0,
////								 getAttrPos((QueryOperator *) clean, n->attrName), 0, n->dataType);
////		RJoinAttrs = appendToTailOfList(RJoinAttrs, ar);
//		JoinAttrNames = appendToTailOfList(JoinAttrNames, n->attrName);
//	}

	FOREACH(AttributeDef, L, so->op.schema->attrDefs)
	{
		FOREACH(AttributeDef, R, clean->op.schema->attrDefs)
		{
			if(streq(L->attrName, R->attrName))
			{
				AttributeReference *arL = createFullAttrReference(L->attrName, 0,
							getAttrPos((QueryOperator *) so, L->attrName), 0, L->dataType);
				AttributeReference *arR = createFullAttrReference(R->attrName, 1,
							getAttrPos((QueryOperator *) clean, R->attrName), 0, R->dataType);

				//creating is null expression for left side
				Node *condN = (Node *) createIsNullExpr((Node *) arL);
				//creating left and right expression for both left and right side
				Node *condEq = (Node *) createOpExpr(OPNAME_EQ, LIST_MAKE(arL, arR));
				// creating the OR condition
				Node *cond = (Node *) createOpExpr(OPNAME_OR, LIST_MAKE(condN, condEq));

				joinList = appendToTailOfList(joinList, cond);
			}
		}
	}

//	joinCondt = (Node *) createOpExpr(OPNAME_AND, joinList);
	joinCondt = (Node *) createOpExpr(OPNAME_AND, joinList);

//	List *inputs = CONCAT_LISTS(LJoinAttrs,RJoinAttrs);
//	List *inputs = CONCAT_LISTS(so, clean);

//	QueryOperator *joinOp = (QueryOperator *) createJoinOp(JOIN_FULL_OUTER, joinCondt, inputs, NIL, JoinAttrNames);

	QueryOperator *copyClean = copyObject(clean);
	List *allInput = LIST_MAKE((QueryOperator *) so, copyClean);
	JoinAttrNames = CONCAT_LISTS(getAttrNames(inform->op.schema), getAttrNames(clean->op.schema));
	QueryOperator *joinOp = (QueryOperator *) createJoinOp(JOIN_INNER, joinCondt, allInput, NIL, JoinAttrNames);

	makeAttrNamesUnique((QueryOperator *) joinOp);
	SET_BOOL_STRING_PROP(joinOp, PROP_MATERIALIZE);

	addParent(copyClean, joinOp);
	addParent((QueryOperator *) so, joinOp);

	switchSubtrees((QueryOperator *) so, (QueryOperator *) joinOp);
	DEBUG_NODE_BEATIFY_LOG("Join Patterns with Data: ", joinOp);


	// Add projection to exclude unnecessary attributes
	List *projExprs = NIL;
	List *attrNames = NIL;
	List *allAttrs = NIL;
	List *unNecAttr = NIL;
	int beginPos = 0;
	int endPos = 0;

	// store output attributes
	FOREACH(AttributeDef, a, joinOp->schema->attrDefs)
	{
		beginPos++;

		if(streq(a->attrName,COVERAGE))
			break;
	}

	FOREACH(AttributeDef, a, joinOp->schema->attrDefs)
	{
		if(isPrefix(a->attrName,VALUE_IG))
			break;

		endPos++;
	}

	allAttrs = copyObject(joinOp->schema->attrDefs);
	unNecAttr = sublist(allAttrs, beginPos, endPos-1);

//	FOREACH(AttributeDef, a, joinOp->schema->attrDefs)
//	{
//		char *subAttrName = substr(a->attrName,1,strlen(a->attrName)-2);
//
//		if(isPrefix(a->attrName,INDEX) &&
//				isSuffix(subAttrName,"1"))
//		{
//			unNecAttr = appendToTailOfList(unNecAttr, a->attrName);
//		}
//	}

	FOREACH(AttributeDef, a, joinOp->schema->attrDefs)
	{
//		if(!searchListString(unNecAttr,a->attrName))
		if(!searchListNode(unNecAttr,(Node *) a))
		{
			AttributeReference *ar = createFullAttrReference(a->attrName, 0,
					getAttrPos((QueryOperator *) joinOp, a->attrName), 0, a->dataType);

			projExprs = appendToTailOfList(projExprs,ar);
			attrNames = appendToTailOfList(attrNames,ar->name);
		}
	}

	ProjectionOperator *po = createProjectionOp(projExprs, NULL, NIL, attrNames);
	addChildOperator((QueryOperator *) po, (QueryOperator *) joinOp);
	switchSubtrees((QueryOperator *) joinOp, (QueryOperator *) po);
	SET_BOOL_STRING_PROP(po, PROP_MATERIALIZE);


	// Adding duplicate elimination
	projExprs = NIL;
	List *attrDefs = po->op.schema->attrDefs;

	FOREACH(AttributeDef, a, attrDefs)
	{
		AttributeReference *ar = createFullAttrReference(a->attrName, 0,
				getAttrPos((QueryOperator *) po, a->attrName), 0, a->dataType);

		projExprs = appendToTailOfList(projExprs,ar);
	}

	QueryOperator *dr = (QueryOperator *) createDuplicateRemovalOp(projExprs, (QueryOperator *) po, NIL, getAttrDefNames(attrDefs));
	addParent((QueryOperator *) po,dr);
	switchSubtrees((QueryOperator *) po, (QueryOperator *) dr);
	SET_BOOL_STRING_PROP(dr, PROP_MATERIALIZE);

	//Adding CODE FOR R^2 here for testing purposes this will move after JOIN/ get data
	List *aggrsAnalysis = NIL;
	List *groupByAnalysis = NIL;
	List *analysisCorrNames = NIL;

	AttributeReference *arDist = createFullAttrReference("Total_Distance", 0,
							 getAttrPos(dr, "Total_Distance"), 0, DT_INT);

	FOREACH(AttributeDef, n, dr->schema->attrDefs)
	{
		if(isPrefix(n->attrName, "value"))
		{
			int len = strlen(n->attrName) - 1;
			char *name = substr(n->attrName, 14, len);
			analysisCorrNames = appendToTailOfList(analysisCorrNames, CONCAT_STRINGS(name, "_r2"));
		}
	}

	FOREACH(AttributeDef, n, dr->schema->attrDefs)
	{
		if(isPrefix(n->attrName, "value"))
		{
			List *functioninput = NIL;
			AttributeReference *ar = createFullAttrReference(n->attrName, 0,
									 getAttrPos(dr, n->attrName), 0, n->dataType);

			functioninput = appendToTailOfList(functioninput, ar);
			functioninput = appendToTailOfList(functioninput, arDist);
			FunctionCall *r_2 = createFunctionCall("regr_r2", functioninput);
			FunctionCall *coalesce = createFunctionCall("COALESCE", LIST_MAKE(r_2, createConstInt(0)));
			aggrsAnalysis = appendToTailOfList(aggrsAnalysis, coalesce);
		}
		else if(!isPrefix(n->attrName, "Total"))
		{
			AttributeReference *ar = createFullAttrReference(n->attrName, 0,
									 getAttrPos(dr, n->attrName), 0, n->dataType);
			groupByAnalysis = appendToTailOfList(groupByAnalysis, ar);
			analysisCorrNames = appendToTailOfList(analysisCorrNames, n->attrName);
		}
	}

	AggregationOperator *analysisAggr = createAggregationOp(aggrsAnalysis, groupByAnalysis, NULL, NIL, analysisCorrNames);
//	ProjectionOperator *test = createProjectionOp(analysisCorr, NULL, NIL, analysisCorrNames);
	addChildOperator((QueryOperator *) analysisAggr, (QueryOperator *) dr);
	switchSubtrees((QueryOperator *) dr, (QueryOperator *) analysisAggr);

	LOG_RESULT("Rewritten Pattern Generation tree for patterns", analysisAggr);

	return analysisAggr;
}



static QueryOperator *
rewriteIG_Analysis (AggregationOperator *patterns)
{
	List *projExprs = NIL;
	List *projNames = NIL;
	List *meanr2Exprs = NIL;
	int pos = 0;


	FOREACH(AttributeDef, n, patterns->op.schema->attrDefs)
	{
		if(isSuffix(n->attrName, "r2"))
		{
			AttributeReference *ar = createFullAttrReference(n->attrName, 0,
								pos, 0, n->dataType);
			projExprs = appendToTailOfList(projExprs, ar);
			meanr2Exprs = appendToTailOfList(meanr2Exprs, ar);
			projNames = appendToTailOfList(projNames, n->attrName);
			pos = pos + 1;
		}
	}

	FOREACH(AttributeDef, n, patterns->op.schema->attrDefs)
	{
		if(!isSuffix(n->attrName, "r2"))
		{
			AttributeReference *ar = createFullAttrReference(n->attrName, 0,
								pos, 0, n->dataType);
			projExprs = appendToTailOfList(projExprs, ar);
			projNames = appendToTailOfList(projNames, n->attrName);
			pos = pos + 1;
		}
	}

	int l = LIST_LENGTH(meanr2Exprs);
	Node *meanr2 = (Node *) (createOpExpr("/", LIST_MAKE(createOpExpr("+", meanr2Exprs), createConstInt(l))));
	projExprs = appendToTailOfList(projExprs, meanr2);
	projNames = appendToTailOfList(projNames, "mean_r2");

	ProjectionOperator *analysis = createProjectionOp(projExprs, NULL, NIL, projNames);
	addChildOperator((QueryOperator *) analysis, (QueryOperator *) patterns);
	switchSubtrees((QueryOperator *) patterns, (QueryOperator *) analysis);


	List *fscoreExprs = NIL;
	List *fscoreNames = NIL;
	List *sumExprs = NIL;
	List *prodExprs = NIL;

	FOREACH(AttributeDef, n, analysis->op.schema->attrDefs)
	{
		AttributeReference *ar = createFullAttrReference(n->attrName, 0,
							getAttrPos((QueryOperator *) analysis, n->attrName), 0, n->dataType);

		fscoreExprs = appendToTailOfList(fscoreExprs, ar);
		fscoreNames = appendToTailOfList(fscoreNames, n->attrName);
	}

	FOREACH(AttributeDef, n, analysis->op.schema->attrDefs)
	{
		if(!isPrefix(n->attrName, "i") && !isSuffix(n->attrName, "r2"))
		{
		AttributeReference *ar = createFullAttrReference(n->attrName, 0,
							getAttrPos((QueryOperator *) analysis, n->attrName), 0, n->dataType);
		sumExprs = appendToTailOfList(sumExprs, ar);
		prodExprs = appendToTailOfList(prodExprs, ar);
		}
//		else if(streq(n->attrName, "informativeness"))
//		{
//			AttributeReference *ar = createFullAttrReference("informativeness", 0,
//								getAttrPos((QueryOperator *) analysis, "informativeness"), 0, n->dataType);
//			sumExprs = appendToTailOfList(sumExprs, ar);
//			prodExprs = appendToTailOfList(prodExprs, ar);
//		}
	}

	FOREACH(AttributeDef, n, analysis->op.schema->attrDefs)
	{
		if(streq(n->attrName, "informativeness"))
		{
			AttributeReference *ar = createFullAttrReference(n->attrName, 0,
								getAttrPos((QueryOperator *) analysis, n->attrName), 0, n->dataType);
			sumExprs = appendToTailOfList(sumExprs, ar);
			prodExprs = appendToTailOfList(prodExprs, ar);
		}

		if(streq(n->attrName, "mean_r2"))
		{
			AttributeReference *ar = createFullAttrReference(n->attrName, 0,
								getAttrPos((QueryOperator *) analysis, n->attrName), 0, n->dataType);
			sumExprs = appendToTailOfList(sumExprs, ar);
			prodExprs = appendToTailOfList(prodExprs, ar);
		}
	}

	int fCount = LIST_LENGTH(prodExprs);
	prodExprs = appendToTailOfList(prodExprs, createConstInt(fCount));
	Node *prod = (Node *) (createOpExpr("*", prodExprs));
	Node *sumOp = (Node *) (createOpExpr("+", sumExprs));

	Node *f_score = (Node *) (createOpExpr("/", LIST_MAKE(prod, sumOp)));

	fscoreExprs = appendToTailOfList(fscoreExprs, f_score);
	fscoreNames = appendToTailOfList(fscoreNames, FSCORE);

	QueryOperator *fscore = (QueryOperator *) createProjectionOp(fscoreExprs, NULL, NIL, fscoreNames);
	addChildOperator((QueryOperator *) fscore, (QueryOperator *) analysis);
	switchSubtrees((QueryOperator *) analysis, (QueryOperator *) fscore);

	// add projection for ORDER BY
	pos = 0;
	List *projExpr = NIL;

	FOREACH(AttributeDef,a,fscore->schema->attrDefs)
	{
		AttributeReference *ar = createFullAttrReference(strdup(a->attrName), 0, pos, 0, a->dataType);

		if(streq(a->attrName,FSCORE))
			f_score = (Node *) ar;

		projExpr = appendToTailOfList(projExpr, ar);
		pos++;
	}

	ProjectionOperator *projForOrder = createProjectionOp(projExpr, NULL, NIL, getAttrNames(fscore->schema));
	addChildOperator((QueryOperator *) projForOrder, (QueryOperator *) fscore);
	switchSubtrees((QueryOperator *) fscore, (QueryOperator *) projForOrder);

	// add order by clause
	Node *ordCond = f_score;
	OrderExpr *ordExpr = createOrderExpr(ordCond, SORT_DESC, SORT_NULLS_LAST);
	OrderOperator *ord = createOrderOp(singleton(ordExpr), (QueryOperator *) projForOrder, NIL);

	addParent((QueryOperator *) projForOrder, (QueryOperator *) ord);
	switchSubtrees((QueryOperator *) projForOrder, (QueryOperator *) ord);

	return (QueryOperator *) ord;

}



static QueryOperator *
rewriteIG_Projection (ProjectionOperator *op)
{
    ASSERT(OP_LCHILD(op));
    DEBUG_LOG("REWRITE-IG - Integration");
    DEBUG_LOG("Operator tree \n%s", nodeToString(op));

    // store original attributes in the input query
    List *origAttrs = op->projExprs;

    // temporary expression list to grab the case when from the input
    List *grabCaseExprs = NIL;

	// temporary expression list to grab the case when from the input
    int x = 0;
	FOREACH(AttributeReference, a, op->projExprs)
	{
		if(isA(a, CaseExpr))
		{
			grabCaseExprs = appendToTailOfList(grabCaseExprs, a);
		}
		else
		{
			x++;
		}

	}

	List *asNames = NIL;
	int y = 0;
	FOREACH(AttributeDef, a, op->op.schema->attrDefs)
	{
		if(x != y)
		{
			y ++;
		}
		else
		{
			asNames = appendToTailOfList(asNames, CONCAT_STRINGS(a->attrName, "_case"));
		}
	}

//	asNames = appendToTailOfList(asNames, CONCAT_STRINGS("newName"));


    QueryOperator *child = OP_LCHILD(op);

    // rewrite child
    rewriteIG_Operator(child);

    //TODO: op should be expanded to have ig columns.
// 	switchSubtrees((QueryOperator *) op, child); // child here has join property

	// Getting Table name and length of table name here
	char *tblNameL = "";
	HashMap *attrLNames = NEW_MAP(Constant, Node);
	HashMap *attrRNames = NEW_MAP(Constant, Node);

    List *joinCond = (List *) GET_STRING_PROP(child, PROP_JOIN_ATTRS_FOR_HAMMING);
    List *joinAttrs = NIL;
//    List *attrLeft = copyObject(attrL);
//    List *attrRight = copyObject(attrR);
//    List *joinNotInOpProjExprs = NIL;

    FOREACH(Operator, o, joinCond)
    {
    	FOREACH(AttributeReference, ar, o->args)
		{
//    		AttributeReference *ar = (AttributeReference *) getHeadOfListP(o->args);
    		joinAttrs = appendToTailOfList(joinAttrs, ar->name);

//			AttributeDef *a = makeNode(AttributeDef);
//			a->attrName = ar->name;
//			a->dataType = ar->attrType;
//
//    		if(ar->attrPosition == 0)
//    		{
////    			attrLeft = appendToTailOfList(attrLeft, a);
//
//    			if(!searchListNode(op->projExprs, (Node *) ar))
//    				joinNotInOpProjExprs = appendToTailOfList(joinNotInOpProjExprs, ar);
//    		}

//    		if(ar->attrPosition == 1)
//    			attrRight = appendToTailOfList(attrRight, a);
		}
    }

    FOREACH(AttributeDef, n, attrL)
	{
		if(isPrefix(n->attrName, "ig"))
		{
			int len1 = strlen(n->attrName);
			int len2 = strlen(strrchr(n->attrName, '_'));
			int len = len1 - len2 - 1;
			tblNameL = substr(n->attrName, 8, len);
			tblNameL = CONCAT_STRINGS(tblNameL, "_");
			break;
		}

		MAP_ADD_STRING_KEY(attrLNames, n->attrName, n);
	}

	char *tblNameR = "";
	FOREACH(AttributeDef, n, attrR)
	{
		if(isPrefix(n->attrName, "ig"))
		{
			int len1 = strlen(n->attrName);
			int len2 = strlen(strrchr(n->attrName, '_'));
			int len = len1 - len2 - 1;
			tblNameR = substr(n->attrName, 8, len);
			tblNameR = CONCAT_STRINGS(tblNameR, "_");

			break;
		}

		MAP_ADD_STRING_KEY(attrRNames, n->attrName, n);
	}


	List *newProjExpr = NIL;
	List *newAttrNames = NIL;
	HashMap *igAttrs = NEW_MAP(Constant, Node);
//	int pos = 0;
//
//	// this adds the first projection after we come out of join
//	FOREACH(AttributeDef, a, child->schema->attrDefs)
//	{
//		newProjExpr = appendToTailOfList(newProjExpr,
//				 createFullAttrReference(a->attrName, 0, pos, 0, a->dataType));
//
//		newAttrNames = appendToTailOfList(newAttrNames, a->attrName);
//		pos++;
//	}
//

    // add ig attributes
	FOREACH(Node, n, op->projExprs)
	{
		if(isA(n, CaseExpr))
		{
			CaseExpr *ce = (CaseExpr *) n;

			FOREACH(CaseWhen, cw, ce->whenClauses)
			{
				// when condition
				List *whenArgs = ((Operator *) cw->when)->args;

				FOREACH(Node, n, whenArgs)
				{
					if(isA(n, Operator))
					{
						Operator *op = (Operator *) n;
						FOREACH(Node, arg, op->args)
						{
							// this works and changes position for maqi1
							if(isA(arg, AttributeReference))
							{
								AttributeReference *ar = (AttributeReference *) arg;
								ar->attrPosition = getAttrPos((QueryOperator *) child, ar->name);
							}

							// this works and changes the position for gdays
							if(isA(arg, IsNullExpr))
							{
								// this gets the IsNullExpr of node x and stores it in isN
								IsNullExpr *isN = (IsNullExpr *) arg;
								// this takes the expr of IsNullExpr(isN) and stores it in new node ofisN
								Node *ofisN = isN->expr;
								// this gets the AttributeReference in the node(ofisN) and stores it in arofisN
								AttributeReference *arofisN = (AttributeReference *) ofisN;
								arofisN->attrPosition = getAttrPos((QueryOperator *) child, arofisN->name);
							}
						}
					}
				}

				// then
				AttributeReference *then = (AttributeReference *) cw->then;
				then->attrPosition = getAttrPos((QueryOperator *) child, then->name);
			}

			newProjExpr = appendToTailOfList(newProjExpr, n);
		}
		else
		{
			AttributeReference *a = (AttributeReference *) n;
			AttributeReference *ar = createFullAttrReference(a->name, 0,
			    				getAttrPos((QueryOperator *) child, a->name), 0, a->attrType);

			newProjExpr = appendToTailOfList(newProjExpr, ar);
		}
	}

	// add case when statement that merge common attribute value
	List *newProjExprWithCaseWhen = NIL;

	FOREACH(Node, n, newProjExpr)
	{
		if(!isA(n, CaseExpr) || !isA(n, Operator))
		{
			AttributeReference *ar = (AttributeReference *) n;
			if(MAP_HAS_STRING_KEY(attrLNames, ar->name) &&
					MAP_HAS_STRING_KEY(attrRNames, ar->name))
			{
//				AttributeReference *arl = createFullAttrReference(ar->name, 0,
//						getAttrPos((QueryOperator *) child, ar->name), 0, ar->attrType);

				//TODO: find the partner attribute
				char *attrName = CONCAT_STRINGS(ar->name,"1");
				AttributeReference *arr = NULL;

				if(isA((Node *) child, SelectionOperator))
				{
					QueryOperator *grandChild = OP_LCHILD(child);
					arr = createFullAttrReference(attrName, 0,
							getAttrPos((QueryOperator *) grandChild, attrName), 0, ar->attrType);
				}
				else
					arr = getAttrRefByName((QueryOperator *) child, attrName);

				// common value
				Node *cond = (Node *) createOpExpr(OPNAME_EQ, LIST_MAKE(ar,arr));
				Node *then = (Node *) ar;
				CaseWhen *caseWhen1 = createCaseWhen(cond, then);

				// leftside null
				cond = (Node *) createIsNullExpr((Node *) ar);
				then = (Node *) arr;
				CaseWhen *caseWhen2 = createCaseWhen(cond, then);

				// rightside null
				cond = (Node *) createIsNullExpr((Node *) arr);
				then = (Node *) ar;
				CaseWhen *caseWhen3 = createCaseWhen(cond, then);

				// both null
				cond = (Node *)createOpExpr(OPNAME_AND,
						LIST_MAKE(createIsNullExpr((Node *) ar),createIsNullExpr((Node *) arr)));

				if(ar->attrType == DT_STRING || ar->attrType == DT_VARCHAR2)
					then = (Node *) createConstString("na");
				if(ar->attrType == DT_INT || ar->attrType == DT_FLOAT || ar->attrType == DT_LONG)
					then = (Node *) createConstInt(0);

				CaseWhen *caseWhen4 = createCaseWhen(cond, then);

				Node *els = (Node *) ar;
				CaseExpr *caseExpr = createCaseExpr(NULL, LIST_MAKE(caseWhen1,caseWhen2,caseWhen3,caseWhen4), els);
				newProjExprWithCaseWhen = appendToTailOfList(newProjExprWithCaseWhen, caseExpr);
			}
			else
			{
				AttributeReference *ar = (AttributeReference *) n;
				FunctionCall *coalesce = NULL;

				if(ar->attrType == DT_STRING || ar->attrType == DT_VARCHAR2)
					coalesce = createFunctionCall("COALESCE", LIST_MAKE(n, (Node *) createConstString("na")));

				if(ar->attrType == DT_INT || ar->attrType == DT_FLOAT || ar->attrType == DT_LONG)
					coalesce = createFunctionCall("COALESCE", LIST_MAKE(n, (Node *) createConstInt(0)));

				newProjExprWithCaseWhen = appendToTailOfList(newProjExprWithCaseWhen, (Node *) coalesce);
			}
		}
		else
		{
			FunctionCall *coalesce = createFunctionCall("COALESCE", LIST_MAKE(n, createConstInt(0)));
			newProjExprWithCaseWhen = appendToTailOfList(newProjExprWithCaseWhen, (Node *) coalesce);
		}
	}


	FOREACH(AttributeDef, a, op->op.schema->attrDefs)
		newAttrNames = appendToTailOfList(newAttrNames, a->attrName);

    FOREACH(AttributeDef, a, child->schema->attrDefs)
    {
    	if(a->dataType == DT_BIT10)
    	{
    		AttributeReference *ar = createFullAttrReference(a->attrName, 0,
    				getAttrPos((QueryOperator *) child, a->attrName), 0, a->dataType);

    		newProjExprWithCaseWhen = appendToTailOfList(newProjExprWithCaseWhen, ar);
    		newAttrNames = appendToTailOfList(newAttrNames, ar->name);

    		MAP_ADD_STRING_KEY(igAttrs, ar->name, ar);
    	}
    }


    // collect join columns
    List *commonAttrNames = NIL;
    List *commonAttrNamesR = NIL;
    List *joinAttrNames = NIL;
    List *joinAttrNamesR = NIL;

//    List *joinCond = (List *) GET_STRING_PROP(child, PROP_JOIN_ATTRS_FOR_HAMMING);
//    List *joinAttrs = NIL;
//
//    FOREACH(Operator, o, joinCond)
//    {
//    	AttributeReference *ar = (AttributeReference *) getHeadOfListP(o->args);
//    	joinAttrs = appendToTailOfList(joinAttrs, ar->name);
//    }

    // add additional ig columns
    List *addIgExprs = NIL;
    List *addIgAttrs = NIL;

//    // when join attributes are not on the select clause in the original query
//	if(LIST_LENGTH(joinNotInOpProjExprs) != 0)
//	{
//		FOREACH(AttributeReference, ar, joinNotInOpProjExprs)
//		{
//			char *igName = CONCAT_STRINGS("ig_conv_", tblNameL, ar->name);
//			joinAttrNames = appendToTailOfList(joinAttrNames, createConstString(igName));
//
//			char *igNameR = CONCAT_STRINGS("ig_conv_", tblNameR, ar->name);
//			joinAttrNamesR = appendToTailOfList(joinAttrNamesR, createConstString(igNameR));
//		}
//	}

    List *allAttrLR = CONCAT_LISTS(copyObject(attrL), copyObject(attrR));

    FOREACH(AttributeDef, a, allAttrLR)
    {
    	if(!isPrefix(a->attrName,IG_PREFIX) && !isSuffix(a->attrName,"_anno"))
    	{
        	char *igName = CONCAT_STRINGS("ig_conv_",
        			MAP_HAS_STRING_KEY(attrLNames, a->attrName) ? tblNameL : tblNameR, a->attrName);

            if(MAP_HAS_STRING_KEY(attrLNames, a->attrName) &&
            		MAP_HAS_STRING_KEY(attrRNames, a->attrName))
        	{
    			char *igNameR = CONCAT_STRINGS("ig_conv_",
						MAP_HAS_STRING_KEY(attrLNames, a->attrName) ? tblNameR : tblNameL, a->attrName);

    			Constant *constIgName = createConstString(igName);
				Constant *constIgNameR = createConstString(igNameR);

            	if(!searchListString(joinAttrs, a->attrName))
        		{
        			if(!searchListNode(commonAttrNames, (Node *) constIgName))
        				commonAttrNames = appendToTailOfList(commonAttrNames, constIgName);

        			if(!searchListNode(commonAttrNamesR, (Node *) constIgNameR))
            			commonAttrNamesR = appendToTailOfList(commonAttrNamesR, constIgNameR);
        		}
        		else
        		{
        			if(!searchListNode(joinAttrNames, (Node *) constIgName))
        				joinAttrNames = appendToTailOfList(joinAttrNames, constIgName);

					if(!searchListNode(joinAttrNamesR, (Node *) constIgNameR))
            			joinAttrNamesR = appendToTailOfList(joinAttrNamesR, constIgNameR);
        		}
        	}
    	}
    }

    FOREACH(Node, n, op->projExprs)
    {
    	if(!isA(n, CaseExpr))
//    			|| !isPrefix(ar->name,IG_PREFIX))
    	{
    		AttributeReference *ar = (AttributeReference *) n;

    		//TODO: remove unique number in the attr from shared
    		char *origAttrName = replaceSubstr(ar->name,gprom_itoa(1),"");

    		char *igName = CONCAT_STRINGS("ig_conv_",
    									MAP_HAS_STRING_KEY(attrLNames, origAttrName) ? tblNameL : tblNameR, origAttrName);

    		if(MAP_HAS_STRING_KEY(igAttrs, igName))
    		{
    			AttributeReference *igExpr = (AttributeReference *) MAP_GET_STRING(igAttrs, igName);
    			AttributeReference *ar = createFullAttrReference(igExpr->name, 0, igExpr->attrPosition, 0, igExpr->attrType);

    			addIgExprs = appendToTailOfList(addIgExprs, ar);
    			addIgAttrs = appendToTailOfList(addIgAttrs, CONCAT_STRINGS(igName,INTEG_SUFFIX));
    		}

//    		if(MAP_HAS_STRING_KEY(attrLNames, ar->name) &&
//    				MAP_HAS_STRING_KEY(attrRNames, ar->name))
//    		{
//    			if(!searchListString(joinAttrs, ar->name))
//    			{
//    				commonAttrNames = appendToTailOfList(commonAttrNames, createConstString(igName));
//
//    				char *igNameR = CONCAT_STRINGS("ig_conv_",
//    						MAP_HAS_STRING_KEY(attrLNames, ar->name) ? tblNameR : tblNameL, ar->name);
//
//    				commonAttrNamesR = appendToTailOfList(commonAttrNamesR, createConstString(igNameR));
//    			}
//    			else
//    			{
//    				joinAttrNames = appendToTailOfList(joinAttrNames, createConstString(igName));
//
//    				char *igNameR = CONCAT_STRINGS("ig_conv_",
//    						MAP_HAS_STRING_KEY(attrLNames, ar->name) ? tblNameR : tblNameL, ar->name);
//
//    				joinAttrNamesR = appendToTailOfList(joinAttrNamesR, createConstString(igNameR));
//    			}
//    		}
    	}

    	if(isA(n, CaseExpr))
    	{
    		CaseExpr *ce = copyObject((CaseExpr *) n);
    		Node *el = ce->elseRes;
    		AttributeReference *ar = NULL;
    		char *igName = NULL;

    		//TODO: then can be an expression.
			FOREACH(CaseWhen, cw, ce->whenClauses)
			{
				ar = (AttributeReference *) cw->then;
				igName = CONCAT_STRINGS("ig_conv_", MAP_HAS_STRING_KEY(attrLNames, ar->name) ? tblNameL : tblNameR, ar->name);

				if(MAP_HAS_STRING_KEY(igAttrs, igName))
				{
					AttributeReference *igExpr = (AttributeReference *) MAP_GET_STRING(igAttrs, igName);
					cw->then = (Node *) igExpr;
				}
			}

			//TODO: else can be an expression.
			ar = (AttributeReference *) el;
			igName = CONCAT_STRINGS("ig_conv_",
										MAP_HAS_STRING_KEY(attrLNames, ar->name) ? tblNameL : tblNameR,
										ar->name);

			if(MAP_HAS_STRING_KEY(igAttrs, igName))
			{
				AttributeReference *igExpr = (AttributeReference *) MAP_GET_STRING(igAttrs, igName);
				ce->elseRes = (Node *) igExpr;
			}

			addIgExprs = appendToTailOfList(addIgExprs, ce);
			addIgAttrs = appendToTailOfList(addIgAttrs, CONCAT_STRINGS(igName,INTEG_SUFFIX));
    	}
    }

    List *allExprs = CONCAT_LISTS(newProjExprWithCaseWhen,addIgExprs);
    List *allAttrs = CONCAT_LISTS(newAttrNames,addIgAttrs);

	ProjectionOperator *newProj = createProjectionOp(allExprs, NULL, NIL, allAttrs);
    addChildOperator((QueryOperator *) newProj, (QueryOperator *) child);
    switchSubtrees((QueryOperator *) op, (QueryOperator *) newProj);


    // TODO: coalesce becomes DT_STRING
    int pos = 0;
    List *newProjExprs = NIL;

    FOREACH(Node, n, newProj->projExprs)
    {
    	if(isA(n,FunctionCall))
    	{
    		// change the datatype in attrDef to original datatype
    		AttributeDef *a = getAttrDefByPos((QueryOperator *) newProj,pos);
    		QueryOperator *child = (QueryOperator *) getHeadOfListP(newProj->op.inputs);
    		AttributeDef *childa = getAttrDefByName(child,a->attrName);
    		a->dataType = childa->dataType;

    		// apply cast to coalesce
			CastExpr *cast = createCastExpr(n, childa->dataType);
			newProjExprs = appendToTailOfList(newProjExprs, cast);
    	}
    	else
    	{
        	newProjExprs = appendToTailOfList(newProjExprs, n);
    	}

    	pos++;
    }

    newProj->projExprs = newProjExprs;

    // if there is PROP_JOIN_ATTRS_FOR_HAMMING set then copy over the properties to the new proj op
    if(HAS_STRING_PROP(child, PROP_JOIN_ATTRS_FOR_HAMMING))
    {
        SET_STRING_PROP(newProj, PROP_JOIN_ATTRS_FOR_HAMMING,
                copyObject(GET_STRING_PROP(child, PROP_JOIN_ATTRS_FOR_HAMMING)));
    }

    //add property for common attributes
    SET_STRING_PROP(newProj, IG_PROP_JOIN_ATTR, joinAttrNames);
    SET_STRING_PROP(newProj, IG_PROP_JOIN_ATTR_R, joinAttrNamesR);

    SET_STRING_PROP(newProj, IG_PROP_NON_JOIN_COMMON_ATTR, commonAttrNames);
    SET_STRING_PROP(newProj, IG_PROP_NON_JOIN_COMMON_ATTR_R, commonAttrNamesR);

    SET_STRING_PROP(newProj, IG_PROP_ORIG_ATTR, origAttrs);

    INFO_OP_LOG("Rewritten Operator tree for all IG attributes", newProj);



/* TODO: take a look */
//
//    //fixing positions in grabCaseExprs before we do anything
//    // need to edit then and else. Then is in whenClause
//	CaseWhen *whenClause1;
//	Node *elseClause1 = NULL;
//	AttributeReference *then1 = NULL;
//	List *when1 = NULL;
//	char *elsename1 = NULL;
////	char *thenname1 = NULL;
//	List *grabCaseExprs1 = NULL;
//
//	FOREACH(Node, a, grabCaseExprs)
//	{
//		if(isA(a, CaseExpr))
//		{
//
//			whenClause1 = (CaseWhen *) getHeadOfListP(((CaseExpr *) a)->whenClauses);
//
//			when1 = ((Operator *) whenClause1->when)->args;
//
//			FOREACH(Node, a, when1)
//			{
//				if(isA(a, Operator))
//				{
//					Operator *op = (Operator *) a;
//					FOREACH(Node, x, op->args) // op = a
//					{
//						// this works and changes position for maqi1
//						if(isA(x, AttributeReference))
//						{
//							AttributeReference *ar = (AttributeReference *) x;
//							ar->attrPosition = getAttrPos((QueryOperator *) child, ar->name);
//						}
//
//						// this works and changes the position for gdays
//						else if(isA(x, IsNullExpr))
//						{
//							// this gets the IsNullExpr of node x and stores it in isN
//							IsNullExpr *isN = (IsNullExpr *) x;
//							// this takes the expr of IsNullExpr(isN) and stores it in new node ofisN
//							Node *ofisN = isN->expr;
//							// this gets the AttributeReference in the node(ofisN) and stores it in arofisN
//							AttributeReference *arofisN = (AttributeReference *) ofisN;
//							arofisN->attrPosition = getAttrPos((QueryOperator *) child, arofisN->name);
//						}
//					}
//				}
//
//				else if(isA(a, IsNullExpr))
//				{
//					// this gets the IsNullExpr of node x and stores it in isN
//					IsNullExpr *isN = (IsNullExpr *) a;
//					// this takes the expr of IsNullExpr(isN) and stores it in new node ofisN
//					Node *ofisN = isN->expr;
//					// this gets the AttributeReference in the node(ofisN) and stores it in arofisN
//					AttributeReference *arofisN = (AttributeReference *) ofisN;
//					arofisN->attrPosition = getAttrPos((QueryOperator *) child, arofisN->name);
//				}
//
//			}
//
//			//getting then here and fixing the AttributePositions for then
//			then1 = (AttributeReference *) whenClause1->then;
////			then1->attrType = DT_INT;
//			then1->attrPosition = getAttrPos((QueryOperator *) child, then1->name);
//
//			// getting else node from CaseExpr
//			Node *ce = ((CaseExpr *) a)->elseRes;
//			// getting AtributeReference from node else
//			AttributeReference *arce = (AttributeReference *) ce;
//			elsename1 = arce->name;
//			elseClause1 =  (Node *) createFullAttrReference(elsename1, 0,
//					getAttrPos((QueryOperator *) child, elsename1), 0, arce->attrType);
//
//			CaseExpr *caseExpr1 = createCaseExpr(NULL, singleton(whenClause1), elseClause1);
//			grabCaseExprs1 = appendToTailOfList(grabCaseExprs1, caseExpr1);
////			caseList = appendToTailOfList(caseList, caseExprnew);
//
//
//		}
//	}
//
//
//
//    // need to edit then and else. Then is in whenClause
//	CaseWhen *whenClause;
////	CaseWhen *whenClausenew;
//	Node *elseClause = NULL;
//	AttributeReference *then = NULL;
////	AttributeReference *thennew = NULL;
//	List *when = NULL;
//	char *elsename = NULL;
//	char *thenname = NULL;
//	List *caseList = NULL;
//
////	CaseExpr *caseExprnew = NULL;
//
////	CaseWhen *whenClausenew;
////	char *thennew = NULL;
////	char *elsenamenew= NULL;
////	Node *elseClausenew = NULL;
////	char *thennamenew = NULL;
//
//
//	FOREACH(Node, a, grabCaseExprs)
//	{
//		if(isA(a, CaseExpr))
//		{
//
//			/*
//			 * whenClause contains 2 Nodes when and then
//			 * then is a node that contains attribute reference
//			 * when is a node contains Operator
//			 * "then" variable from line 1190 contains AttributeReference
//			 * "when" variable should contain a List of all the args
//			 * there should be 2 args of type OPERATOR in the list
//			 * first operator in the list has name(">") and
//			 * 		 args  and this args contains AttributeReference (maqi1) and a constant
//			 * seond operator in the list has name("NOT") and
//			 * 		 args and this args contains IS_NULL_EXPR which contains expr
//			 * 		 which contains AttributeReference (gdays) which we need to access
//			 *
//			 *
//			 * The bug was coming because the second node in when was not an operator
//			 * It was a IsNullExpr so there was no second Operator which caused the issues
//			 *
//			 */
//
//			//getting when clause here
////			whenClausenew = copyObject((CaseWhen *) getHeadOfListP(((CaseExpr *) a)->whenClauses));
//			whenClause = copyObject((CaseWhen *) getHeadOfListP(((CaseExpr *) a)->whenClauses));
////			whenClausenew = (CaseWhen *) getHeadOfListP(((CaseExpr *) a)->whenClauses);
//			// getting wehn from when clause and fixing the attributePositions
//			when = ((Operator *) whenClause->when)->args;
////			thennew = ((Operator *) whenClausenew->then)->name;
//
//			FOREACH(Node, a, when)
//			{
//				if(isA(a, Operator))
//				{
//					Operator *op = (Operator *) a;
//					FOREACH(Node, x, op->args) // op = a
//					{
//						// this works and changes position for maqi1
//						if(isA(x, AttributeReference))
//						{
//							AttributeReference *ar = (AttributeReference *) x;
//							ar->attrPosition = getAttrPos((QueryOperator *) child, ar->name);
//						}
//
//						// this works and changes the position for gdays
//						else if(isA(x, IsNullExpr))
//						{
//							// this gets the IsNullExpr of node x and stores it in isN
//							IsNullExpr *isN = (IsNullExpr *) x;
//							// this takes the expr of IsNullExpr(isN) and stores it in new node ofisN
//							Node *ofisN = isN->expr;
//							// this gets the AttributeReference in the node(ofisN) and stores it in arofisN
//							AttributeReference *arofisN = (AttributeReference *) ofisN;
//							arofisN->attrPosition = getAttrPos((QueryOperator *) child, arofisN->name);
//						}
//					}
//				}
//
//				else if(isA(a, IsNullExpr))
//				{
//					// this gets the IsNullExpr of node x and stores it in isN
//					IsNullExpr *isN = (IsNullExpr *) a;
//					// this takes the expr of IsNullExpr(isN) and stores it in new node ofisN
//					Node *ofisN = isN->expr;
//					// this gets the AttributeReference in the node(ofisN) and stores it in arofisN
//					AttributeReference *arofisN = (AttributeReference *) ofisN;
//					arofisN->attrPosition = getAttrPos((QueryOperator *) child, arofisN->name);
//				}
//
//			}
//
//			//getting then here and fixing the AttributePositions for then
//			then = (AttributeReference *) whenClause->then;
//			char *namethen = CONCAT_STRINGS("ig_conv_", tblNameR);
//			thenname = CONCAT_STRINGS(namethen , then->name); // then
//			then->name = thenname;
//			then->attrType = DT_BIT10;
//			then->attrPosition = getAttrPos((QueryOperator *) child, thenname);
//
//
////			thennew = (AttributeReference *) whenClausenew->then;
////			thennamenew = substr(thennew->name, 16, 18);
////			thennew->name = thennamenew;
////			thennew->attrType = DT_INT;
////			thennew->attrPosition = getAttrPos((QueryOperator *) newProj, thennamenew);
//
//			char *nameelse = CONCAT_STRINGS("ig_conv_", tblNameL);
//			// getting else node from CaseExpr
//			Node *ce = ((CaseExpr *) a)->elseRes;
//			// getting AtributeReference from node else
//			AttributeReference *arce = (AttributeReference *) ce;
//			elsename = CONCAT_STRINGS(nameelse, arce->name);
//
////			elsenamenew = arce->name;
//
//
////			elseClausenew = (Node *) createFullAttrReference(elsenamenew, 0,
////					getAttrPos((QueryOperator *) newProj, elsenamenew), 0, DT_INT);
////			CaseExpr *caseExprnew = createCaseExpr(NULL, singleton(whenClause), elseClausenew);
//
//
//			elseClause =  (Node *) createFullAttrReference(elsename, 0,
//					getAttrPos((QueryOperator *) child, elsename), 0, DT_BIT10);
//			CaseExpr *caseExpr = createCaseExpr(NULL, singleton(whenClause), elseClause);
//
//
////			elseClausenew =  (Node *) createFullAttrReference(elsenamenew, 0,
////					getAttrPos((QueryOperator *) newProj, elsenamenew), 0, DT_INT);
////			CaseExpr *caseExprnew = createCaseExpr(NULL, singleton(whenClausenew), elseClausenew);
//
//			caseList = appendToTailOfList(caseList, caseExpr);
////			caseList = appendToTailOfList(caseList, caseExprnew);
//
//		}
//	}
//
//	ProjectionOperator *caseWhenList = createProjectionOp(CONCAT_LISTS(allExprs,caseList), NULL, NIL, CONCAT_LISTS(newAttrNames,asNames));
//    addChildOperator((QueryOperator *) caseWhenList, (QueryOperator *) newProj);
//    switchSubtrees((QueryOperator *) newProj, (QueryOperator *) caseWhenList);
//
//
//	List *newOrderExpr = NIL;
//	List *newOrderNames = NIL;
//	List *oldExprs = NIL;
//	List *oldNames = NIL;
////	int orderPos = 0;
////	int t = 0;
//
//	List *attrDefsName = NIL;
//
//	FOREACH(AttributeDef, n, caseWhenList->op.schema->attrDefs)
//	{
//		attrDefsName = appendToTailOfList(attrDefsName, n->attrName);
//	}
//
//    //reordering Projection puts old dayswaqi in the end and replaces the new one with the casewhen
//	FOREACH(AttributeDef, a, caseWhenList->op.schema->attrDefs)
//	{
//		FOREACH(char, n, asNames)
//		{
//			int l1 = strlen(n);
//			int l2 = strlen(strchr(n, '_'));
//			int l = l1-l2-2;
//			char *name = substr(n, 0, l);
//			// we can remove the _new from here this is just here to show in the meeting
////			char *namenew = CONCAT_STRINGS(name, "_new");
//
//			int pos = listPosString(attrDefsName, n);
//			AttributeReference *ar = (AttributeReference *) getNthOfListP(caseWhenList->projExprs, pos);
//
//			//fixing jsut the attribute
//			if(streq(a->attrName, name))
//			{
//				//getting the case when from grabCaseExprs List which is the new caseExprList
//				FOREACH(AttributeReference, a, grabCaseExprs1)
//				{
//					newOrderExpr = appendToTailOfList(newOrderExpr, a);
////					newOrderNames = appendToTailOfList(newOrderNames, namenew);
//					newOrderNames = appendToTailOfList(newOrderNames, name);
//				}
//
//
////				t = orderPos;
////				orderPos++;
//			}
//			//fixing ig attribute adding the new attribute here / adding the new attribute
//			else if(isPrefix(a->attrName, "ig"))
//			{
//				int l1a = strlen(a->attrName) - 1;
//				int l2a = strlen(strrchr(a->attrName, '_'));
//				int la = l1a - l2a + 2;
//				char *namea = substr(a->attrName, la, l1a);
//				char *nameFull = CONCAT_STRINGS("ig_conv_", tblNameL);
//				char *nameFulla = CONCAT_STRINGS(nameFull, name);
//				// adding the new ig attribute here
//				if(strcmp(name, namea) == 0 )
//				{
//					newOrderExpr = appendToTailOfList(newOrderExpr, ar);
//					newOrderNames = appendToTailOfList(newOrderNames, nameFulla);
////					orderPos++;
//				}
//				else
//				{
//					newOrderExpr = appendToTailOfList(newOrderExpr,
//									 createFullAttrReference(a->attrName, 0,
//											 getAttrPos((QueryOperator *) caseWhenList, a->attrName), 0, a->dataType));
//
//					newOrderNames = appendToTailOfList(newOrderNames, a->attrName);
////					orderPos++;
//				}
//			}
//			else if(isSuffix(a->attrName, "case"))
//			{
//				continue;
//			}
//			else
//			{
//				newOrderExpr = appendToTailOfList(newOrderExpr,
//								 createFullAttrReference(a->attrName, 0,
//										 getAttrPos((QueryOperator *) caseWhenList, a->attrName), 0, a->dataType));
//
//				newOrderNames = appendToTailOfList(newOrderNames, a->attrName);
////				orderPos++;
//			}
//		}
//
//	}
//
//	FOREACH(AttributeDef, a, caseWhenList->op.schema->attrDefs)
//	{
//		FOREACH(char, n, asNames)
//		{
//			int l1 = strlen(n);
//			int l2 = strlen(strchr(n, '_'));
//			int l = l1-l2-2;
//			char *name = substr(n, 0, l);
//			char *nameold = CONCAT_STRINGS(name, "_old");
//
//			//adding the old attribute in the end
//			if(strcmp(a->attrName, name) == 0)
//			{
////				newOrderExpr = appendToTailOfList(newOrderExpr,
////								 createFullAttrReference(name, 0,
////										 getAttrPos((QueryOperator *) caseWhenList, a->attrName), 0, a->dataType));
////
////				newOrderNames = appendToTailOfList(newOrderNames, nameold);
////
//
//				oldExprs = appendToTailOfList(oldExprs,
//								 createFullAttrReference(name, 0,
//										 getAttrPos((QueryOperator *) caseWhenList, a->attrName), 0, a->dataType));
//
//				oldNames = appendToTailOfList(oldNames, nameold);
//
//
//			}
//			// pushing old ig attribute in the end
//			else if(isPrefix(a->attrName, "ig"))
//			{
//				int l1a = strlen(a->attrName) - 1;
//				int l2a = strlen(strrchr(a->attrName, '_'));
//				int la = l1a - l2a + 2;
//				char *namea = substr(a->attrName, la, l1a);
//				char *newName = CONCAT_STRINGS(a->attrName, "_old");
//
//				if(strcmp(name, namea) == 0 )
//				{
////					newOrderExpr = appendToTailOfList(newOrderExpr,
////									 createFullAttrReference(a->attrName, 0,
////											 getAttrPos((QueryOperator *) caseWhenList, a->attrName), 0, a->dataType));
////
////					newOrderNames = appendToTailOfList(newOrderNames, newName);
////					orderPos++;
//
//
//					oldExprs = appendToTailOfList(oldExprs,
//									 createFullAttrReference(a->attrName, 0,
//											 getAttrPos((QueryOperator *) caseWhenList, a->attrName), 0, a->dataType));
//
//					oldNames = appendToTailOfList(oldNames, newName);
//
//
//				}
//			}
//		}
//	}



	//now need to fix the old and new ig attributes
//	newOrderExpr = CONCAT_LISTS(newOrderExpr, oldExprs);
//	newOrderNames = CONCAT_LISTS(newOrderNames, oldNames);
//
//
//	ProjectionOperator *order = createProjectionOp(newOrderExpr, NULL, NIL, newOrderNames);
//
//    // if there is PROP_JOIN_ATTRS_FOR_HAMMING set then copy over the properties to the new proj op
//    if(HAS_STRING_PROP(child, PROP_JOIN_ATTRS_FOR_HAMMING))
//    {
//        SET_STRING_PROP(order, PROP_JOIN_ATTRS_FOR_HAMMING,
//                copyObject(GET_STRING_PROP(child, PROP_JOIN_ATTRS_FOR_HAMMING)));
//    }
//
//    addChildOperator((QueryOperator *) order, (QueryOperator *) caseWhenList);
//    switchSubtrees((QueryOperator *) caseWhenList, (QueryOperator *) order);
//    LOG_RESULT("REORDETING TEST ----------------------", order);
//
    // This function creates hash maps and adds hamming distance functions
	ProjectionOperator *hammingvalue_op = rewriteIG_HammingFunctions(newProj);


//	 This function adds the + expression to calculate the total distance
	ProjectionOperator *sumrows = rewriteIG_SumExprs(hammingvalue_op);
//
//	LOG_RESULT("Rewritten Projection Operator tree", hammingvalue_op);
//	return (QueryOperator *) hammingvalue_op;

	AggregationOperator *patterns = rewriteIG_PatternGeneration(sumrows);

	QueryOperator *analysis = rewriteIG_Analysis(patterns);

	INFO_OP_LOG("Rewritten Operator tree for patterns", analysis);
	return analysis;

}




static QueryOperator *
rewriteIG_Join (JoinOperator *op)
{
    DEBUG_LOG("REWRITE-IG - Join");

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


    List *attrLists = ((Operator *) op->cond)->args;
    List *attrNames = NIL;
    boolean isSingle = FALSE;

    FOREACH(Node, n, attrLists)
    	if(isA(n, AttributeReference))
    		isSingle = TRUE;

    if(isSingle)
    	SET_STRING_PROP(op, PROP_JOIN_ATTRS_FOR_HAMMING, singleton(op->cond));
    else
    {
        FOREACH(Node, n, attrLists) {
         	attrNames = appendToTailOfList(attrNames, n);
        }

        SET_STRING_PROP(op, PROP_JOIN_ATTRS_FOR_HAMMING, attrNames);
    }

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
