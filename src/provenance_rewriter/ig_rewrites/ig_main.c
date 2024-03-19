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
#include "provenance_rewriter/ig_rewrites/ig_functions.h"
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

#define INDEX "i_"
#define IG_PREFIX "ig_"
#define VALUE_IG "value_"
#define INTEG_SUFFIX "_integ"
#define ANNO_SUFFIX "_anno"
#define HAMMING_PREFIX "hamming_"
#define PATTERN_IG "pattern_IG"
#define TOTAL_DIST "Total_Distance"
#define AVG_DIST "Average_Distance"
#define COVERAGE "coverage"
#define INFORMATIVENESS "informativeness"
#define PATTERNIG "pattern_IG"
#define FSCORE "f_score"
#define FSCORETOPK "fscoreTopK"
#define MINFSCORETOPK "minfscoreTopK"


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
static boolean explFlag;
static boolean igFlag;
static Node *topk;

QueryOperator *
rewriteIG (ProvenanceComputation  *op)
{
    START_TIMER("rewrite - IG rewrite");

    // unset relation name counters
    nameState = (RelCount *) NULL;
    DEBUG_NODE_BEATIFY_LOG("*************************************\nREWRITE INPUT\n"
            "******************************\n", op);

    //mark the number of table - used in provenance scratch
    markNumOfTableAccess((QueryOperator *) op);

    QueryOperator *newRoot = OP_LCHILD(op);
    DEBUG_NODE_BEATIFY_LOG("rewRoot is:", newRoot);

    igFlag = op->igFlag;
    explFlag = op->explFlag;
    topk = op->topk;

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

    // store the join query
    SET_STRING_PROP(op, PROP_JOIN_OP_IG, OP_LCHILD(op));

    // rewrite child first
    rewriteIG_Operator(child);

    // update selection
	Operator *cond = (Operator *) op->cond;

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
		}
	}

	op->op.schema->attrDefs = child->schema->attrDefs;

	// if there is PROP_JOIN_ATTRS_FOR_HAMMING set then copy over the properties to the new proj op
	if(HAS_STRING_PROP(child, PROP_JOIN_ATTRS_FOR_HAMMING))
	{
		SET_STRING_PROP(op, PROP_JOIN_ATTRS_FOR_HAMMING,
				copyObject(GET_STRING_PROP(child, PROP_JOIN_ATTRS_FOR_HAMMING)));
	}


    LOG_RESULT("Rewritten Selection Operator tree", op);
    return (QueryOperator *) op;
}

//rewriteIG_Conversion
static QueryOperator *
rewriteIG_Conversion (ProjectionOperator *op)
{
	List *newProjExprs = NIL;
	List *projExprs = NIL;
	List *attrNames = NIL;

	newProjExprs = toAsciiList(op);
	op->projExprs = newProjExprs;

	// CREATING a projection to not feed ascii expression into aggregation
	FOREACH(AttributeDef, a, op->op.schema->attrDefs)
	{
		if(isPrefix(a->attrName, "ig") && a->dataType == DT_STRING)
		{
			a->dataType = DT_INT;
		}
	}

	projExprs = getARfromAttrDefs(op->op.schema->attrDefs);
	attrNames = getNamesfromAttrDefs(op->op.schema->attrDefs);

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
	int i = 0;

	FOREACH(Node, n, newProjExprs)
	{
		if(isA(n,Ascii))
		{
			char *attrName = getAttrNameByPos((QueryOperator *) po, i);
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
	aggrs = getAsciiAggrs(newProjExprs, po);
	AggregationOperator *ao = createAggregationOp(aggrs , groupBy, NULL, NIL, newNames);

	addChildOperator((QueryOperator *) ao, (QueryOperator *) po);
	// Switch the subtree with this newly created projection operator.
	switchSubtrees((QueryOperator *) po, (QueryOperator *) ao);

	// CREATING THE NEW PROJECTION OPERATOR
	projExprs = NIL;
	projExprs = getARfromAttrDefs(ao->op.schema->attrDefs);

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
		{
			newProjExprs = appendToTailOfList(newProjExprs, a);
		}

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

	projExprs = getARfromAttrDefswPos((QueryOperator *) newPo, po->op.schema->attrDefs);
	newNames = getNamesfromAttrDefs(po->op.schema->attrDefs);

	ProjectionOperator *addPo = createProjectionOp(projExprs, NULL, NIL, newNames);;

	// Getting Table name and length of table name here
	char *tableName = NULL;
	tableName = getTableNamefromPo(addPo);

	int temp = 0;
	int tableLength = strlen(tableName);
	attrNames = NIL;
	List *newProjExpr = NIL;
	List *newProjExpr1 = NIL;
	List *newProjExpr2 = NIL;


	// Getting original attributes
	newProjExpr1 = getARfromPoAr(addPo);
	attrNames = getNamesfromPoAr(addPo);
	// Creating _anno Attribute
	FOREACH(AttributeReference, n, addPo->projExprs)
	{

		if(temp == 0)
		{
			newProjExpr = appendToTailOfList(newProjExpr, createConstString(tableName));
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
					createConstString((substr(n->name, 9 + tableLength, 9 + tableLength + end - 2))));
		}
	}

	attrNames = appendToTailOfList(attrNames, CONCAT_STRINGS(tableName, "_anno"));
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

    // store the join query
	SET_STRING_PROP(sumrows, PROP_JOIN_OP_IG,
			copyObject(GET_STRING_PROP(hammingvalue_op, PROP_JOIN_OP_IG)));


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
    List *commonAttrNames = (List *) GET_STRING_PROP((QueryOperator *) newProj, IG_PROP_NON_JOIN_COMMON_ATTR);
    List *commonAttrNamesR = (List *) GET_STRING_PROP((QueryOperator *) newProj, IG_PROP_NON_JOIN_COMMON_ATTR_R);
	List *joinAttrNames = (List *) GET_STRING_PROP((QueryOperator *) newProj, IG_PROP_JOIN_ATTR);
	List *joinAttrNamesR = (List *) GET_STRING_PROP((QueryOperator *) newProj, IG_PROP_JOIN_ATTR_R);
	List *newProjExprs = NIL;
	pos = 0;

    FOREACH(AttributeDef, a, newProj->op.schema->attrDefs)
    {
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
    		}

        	// apply case when for original ig columns
        	if(!isSuffix(a->attrName,INTEG_SUFFIX))
        	{
        		origIgInteg = (AttributeReference *) n;
        		char *igOrigNameInteg = origIgInteg->name;

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

	FOREACH(AttributeDef, n, newProj->op.schema->attrDefs)
	{
		List *functioninput = NIL;
		List *cast = NIL;

		if(isPrefix(n->attrName, IG_PREFIX) && isSuffix(n->attrName, INTEG_SUFFIX))
		{
			char *origNameOfInteg = replaceSubstr(n->attrName,INTEG_SUFFIX,"");

			if(MAP_HAS_STRING_KEY(nameToIgAttrRef, origNameOfInteg))
			{

				AttributeReference *attrIgL = getAttrRefByName((QueryOperator *) newProj, n->attrName);
				AttributeReference *attrIgR = getAttrRefByName((QueryOperator *) newProj, origNameOfInteg);

				AttributeDef *origAttrDef = getAttrDefByName((QueryOperator *) newProj, origNameOfInteg);

				if(!searchListNode(commonAttrNames, (Node *) origAttrDef) &&
						!searchListNode(joinAttrNames, (Node *) origAttrDef) &&
							searchListNode(attrR, (Node *) origAttrDef))
				{
					CastExpr *castL;
					castL = createCastExpr((Node *) attrIgL, DT_STRING);
					cast = LIST_MAKE(castL, createConstString("0000000000"));

					FunctionCall *hammingdist = createFunctionCall("hammingdist", cast);
					exprs = appendToTailOfList(exprs,hammingdist);
					atNames = appendToTailOfList(atNames, CONCAT_STRINGS(HAMMING_PREFIX, n->attrName));
				}
				else
				{
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
				}

			}

		}
	}


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

    // store the join query
	SET_STRING_PROP(hamming_op, PROP_JOIN_OP_IG,
			copyObject(GET_STRING_PROP(newProj, PROP_JOIN_OP_IG)));


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
			FunctionCall *hammingdistvalue = createFunctionCall("hammingdistvalue", singleton(a));

			h_valueExprs = appendToTailOfList(h_valueExprs, hammingdistvalue);
			h_valueName = appendToTailOfList(h_valueName, CONCAT_STRINGS(VALUE_IG, a->name));
		}

		posV++;
	}

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

    // store the join query
	SET_STRING_PROP(hammingvalue_op, PROP_JOIN_OP_IG,
			copyObject(GET_STRING_PROP(hamming_op, PROP_JOIN_OP_IG)));


	return hammingvalue_op;
}

static AggregationOperator *
rewriteIG_PatternGeneration (ProjectionOperator *sumrows)
{

	ASSERT(OP_LCHILD(sumrows));
	DEBUG_LOG("REWRITE-IG - Pattern Generation");
	DEBUG_LOG("Operator tree \n%s", nodeToString(sumrows));

	List *Laggrs = NIL;;
	List *Raggrs = NIL;
	List *LaggrsNames = NIL;
	List *RaggrsNames = NIL;

	FOREACH(AttributeDef, n, attrL)
	{
		if(!isPrefix(n->attrName, IG_PREFIX))
		{
			if(!isSuffix(n->attrName, ANNO_SUFFIX))
			{
				Laggrs = appendToTailOfList(Laggrs, n);
				LaggrsNames = appendToTailOfList(LaggrsNames, n->attrName);
			}
		}
	}

	FOREACH(AttributeDef, n, attrR)
	{
		if(!isPrefix(n->attrName, IG_PREFIX))
		{
			if(!isSuffix(n->attrName, ANNO_SUFFIX))
			{
				Raggrs = appendToTailOfList(Raggrs, n);
				RaggrsNames = appendToTailOfList(RaggrsNames, n->attrName);
			}
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


					if(arL->attrPosition != -1)
					{
						cleanExprs = appendToTailOfList(cleanExprs, arL);
						cleanNames = appendToTailOfList(cleanNames, CONCAT_STRINGS(INDEX, LAttrName));
					}
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

	// add ig columns and rowIG
	FOREACH(AttributeReference, n, sumrows->projExprs)
	{
		if(isPrefix(n->name, VALUE_IG))
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

	FOREACH(AttributeDef, n, clean->op.schema->attrDefs)
	{
		//this one makes pattern_IG
		if(streq(n->attrName, TOTAL_DIST))
		{
			AttributeReference *ar = createFullAttrReference(n->attrName, 0,
					   				 getAttrPos((QueryOperator *) clean, n->attrName), 0, n->dataType);
			sum = createFunctionCall("SUM", singleton(ar));
			sum->isAgg = TRUE;

			aggrs = appendToTailOfList(aggrs,sum);
			projNames = appendToTailOfList(projNames, strdup(PATTERN_IG));
		}
	}

	// coverage
	Constant *countProv = createConstInt(1);
	FunctionCall *count = createFunctionCall("COUNT", singleton(countProv));
	count->isAgg = TRUE;

	aggrs = appendToTailOfList(aggrs,count);
	projNames = appendToTailOfList(projNames, strdup(COVERAGE));

	FOREACH(AttributeDef, n, clean->op.schema->attrDefs)
	{
		if(isPrefix(n->attrName, strdup(INDEX)))
		{
			groupBy = appendToTailOfList(groupBy,
					  createFullAttrReference(n->attrName, 0,
					  getAttrPos((QueryOperator *) clean, n->attrName), 0, n->dataType));

			projNames = appendToTailOfList(projNames, n->attrName);

		}
	}

	AggregationOperator *ao = createAggregationOp(aggrs, groupBy, (QueryOperator *) clean, NIL, projNames);
	ao->isCube = TRUE;
	ao->isCubeTestList = (Node *) createConstInt(1);


	FOREACH(AttributeDef, n, ao->op.schema->attrDefs)
	{
		if(streq(n->attrName, strdup(PATTERN_IG)) ||
				streq(n->attrName, strdup(COVERAGE)))
		{
			n->dataType = DT_FLOAT;
		}
	}


	addParent((QueryOperator *) clean, (QueryOperator *) ao);
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

		pos++;
	}


	pos = 0;

	FOREACH(AttributeDef, n, ao->op.schema->attrDefs)
	{
		if(streq(n->attrName, PATTERN_IG) ||
				streq(n->attrName, COVERAGE))
		{
			// Adding patern_IG in the new informProj
			informExprs = appendToTailOfList(informExprs,
						  createFullAttrReference(n->attrName, 0,
								  pos, 0, n->dataType));
			informNames = appendToTailOfList(informNames, n->attrName);
		}

		pos++;
	}


	// ADDING INFORMATIVENESS
	pos = 0;
	List *sumExprs = NIL;
	Node *sumExpr = NULL;

	FOREACH(AttributeDef, n , ao->op.schema->attrDefs)
	{
		if(isPrefix(n->attrName, INDEX))
		{

			AttributeReference *ar = createFullAttrReference(n->attrName, 0, pos, 0, n->dataType);

			Node *cond = (Node *) createOpExpr(OPNAME_NOT, singleton(createIsNullExpr((Node *) ar)));
			Node *then = (Node *) (createConstInt(1));
			Node *els = (Node *) (createConstInt(0));


			CaseWhen *caseWhen = createCaseWhen(cond, then);
			CaseExpr *caseExpr = createCaseExpr(NULL, singleton(caseWhen), els);

			sumExprs = appendToTailOfList(sumExprs, caseExpr);
		}

		pos++;

	}

	sumExpr = (Node *) (createOpExpr("+", sumExprs));
	informExprs = appendToTailOfList(informExprs, sumExpr);
	informNames = appendToTailOfList(informNames, strdup(INFORMATIVENESS));

	ProjectionOperator *inform = createProjectionOp(informExprs, (QueryOperator *) ao, NIL, informNames);
	addParent((QueryOperator *) ao, (QueryOperator *) inform);


	switchSubtrees((QueryOperator *) ao, (QueryOperator *) inform);

	INFO_OP_LOG("Generate Patterns While Computing Informativeness and Coverage: ", inform);

	int num_i = 0;

	// counting attributes
	FOREACH(AttributeDef, n, ao->op.schema->attrDefs)
	{
		if(isPrefix(n->attrName, INDEX))
		{
			num_i = num_i + 1;
		}
	}

	AttributeReference *cov = getAttrRefByName((QueryOperator *) inform, COVERAGE);
	AttributeReference *inf = getAttrRefByName((QueryOperator *) inform, INFORMATIVENESS);
	AttributeReference *pattIG = getAttrRefByName((QueryOperator *) inform, PATTERNIG);

	//creating where condition coverage > 1 OR (coverage = 1 AND informativeness = 5)
	//coverage > 1
	Node *covgt1 = (Node *) createOpExpr(OPNAME_GT, LIST_MAKE(cov, createConstInt(1)));

	//coverage = 1
	Node *cov1 = (Node *) createOpExpr(OPNAME_EQ, LIST_MAKE(cov, createConstInt(1)));

	//informativeness = 5
	Node *info5 = (Node *) createOpExpr(OPNAME_EQ, LIST_MAKE(inf, createConstInt(num_i)));

	//coverage = 1 AND informativeness = 5
	Node *subcond = (Node *) createOpExpr(OPNAME_AND, LIST_MAKE(cov1,info5));

	//coverage > 1 OR (coverage = 1 AND informativeness = 5)
	Node *cond = (Node *) createOpExpr(OPNAME_OR, LIST_MAKE(covgt1,subcond));

	//creating patternIG > 0
	Node *pattCondt = (Node *) createOpExpr(OPNAME_GT, LIST_MAKE(pattIG, createConstInt(0)));

	//patternIG > 0 AND coverage > 1 OR (coverage = 1 AND informativeness = 5)
	Node *finalCond = (Node *) createOpExpr(OPNAME_AND, LIST_MAKE(pattCondt, cond));

	// this one has removeNoGoodPatt
	SelectionOperator *removeNoGoodPatt = createSelectionOp(finalCond,
			(QueryOperator *) inform, NIL, getAttrNames(inform->op.schema));

	addParent((QueryOperator *) inform, (QueryOperator *) removeNoGoodPatt);
	switchSubtrees((QueryOperator *) inform, (QueryOperator *) removeNoGoodPatt);

	INFO_OP_LOG("Remove No Good Patterns: ", removeNoGoodPatt);

	//creating topKPattConstPlac
	//where coverage > 1 and informativeness < 5
	//informativeness < 5
	Node *infoLess = (Node *) createOpExpr(OPNAME_LT, LIST_MAKE(inf, createConstInt(num_i)));

	//coverage > 1 and informativeness < 5
	Node *condtopKPattConstPlac = (Node *) createOpExpr(OPNAME_AND, LIST_MAKE(covgt1, infoLess));

	//creating topKPattConstPlac
	QueryOperator *cpRemoveNoGoodPatt = (QueryOperator *) removeNoGoodPatt;

	SelectionOperator *topKPattConstPlac = createSelectionOp(condtopKPattConstPlac,
			cpRemoveNoGoodPatt, NIL, getAttrNames(inform->op.schema));

	addParent((QueryOperator *) cpRemoveNoGoodPatt, (QueryOperator *) topKPattConstPlac);
	switchSubtrees((QueryOperator *) cpRemoveNoGoodPatt, (QueryOperator *) topKPattConstPlac);

	INFO_OP_LOG("Patterns with Constants and Placeholders: ", topKPattConstPlac);

	//creating topKPattOnlyConst
	//subcond : coverage = 1 AND informativeness = 5

	QueryOperator *coRemoveNoGoodPatt = (QueryOperator *) copyObject((QueryOperator *) removeNoGoodPatt);
	SelectionOperator *topKPattOnlyConst = createSelectionOp(subcond, coRemoveNoGoodPatt, NIL, getAttrNames(inform->op.schema));

	addParent((QueryOperator *) coRemoveNoGoodPatt, (QueryOperator *) topKPattOnlyConst);
	switchSubtrees((QueryOperator *) coRemoveNoGoodPatt, (QueryOperator *) topKPattOnlyConst);

	INFO_OP_LOG("Patterns with Only Placeholders: ", topKPattOnlyConst);



	List *topKattr = NIL;
	List *topKattrNames = NIL;
	List *inputTopK = NIL;
	int topKpos = 0;
	//pattern_IG | informativeness | coverage
	FOREACH(AttributeDef, n, topKPattConstPlac->op.schema->attrDefs)
	{
		if((!streq(n->attrName, INFORMATIVENESS)) &&
		   (!streq(n->attrName, COVERAGE)) &&
		   (!streq(n->attrName, PATTERNIG)))
		{
		AttributeReference *ar = createFullAttrReference(n->attrName, 0,
						topKpos, 0, n->dataType);
		topKattr = appendToTailOfList(topKattr, ar);
		topKattrNames = appendToTailOfList(topKattrNames, n->attrName);
		topKpos = topKpos + 1;
		}

		else if(streq(n->attrName, INFORMATIVENESS))
		{
			AttributeReference *ar = createFullAttrReference(n->attrName, 0,
						topKpos, 0, n->dataType);
			topKattr = appendToTailOfList(topKattr, ar);
			topKattrNames = appendToTailOfList(topKattrNames, n->attrName);
			inputTopK = appendToTailOfList(inputTopK, ar);
			topKpos = topKpos + 1;
		}
		else if(streq(n->attrName, COVERAGE))
		{
			AttributeReference *ar = createFullAttrReference(n->attrName, 0,
						topKpos, 0, n->dataType);
			topKattr = appendToTailOfList(topKattr, ar);
			topKattrNames = appendToTailOfList(topKattrNames, n->attrName);
			inputTopK = appendToTailOfList(inputTopK, ar);
			topKpos = topKpos + 1;
		}
		else if(streq(n->attrName, PATTERNIG))
		{
			AttributeReference *ar = createFullAttrReference(n->attrName, 0,
						topKpos, 0, n->dataType);
			topKattr = appendToTailOfList(topKattr, ar);
			topKattrNames = appendToTailOfList(topKattrNames, n->attrName);
			inputTopK = appendToTailOfList(inputTopK, ar);
			topKpos = topKpos + 1;
		}
	}

	//patternIG * coverage * informativeness
	Node *prodK = (Node *) (createOpExpr(OPNAME_MULT, inputTopK));

	//3 * patternIG * coverage * informativeness
	Node *prod3K = (Node *) (createOpExpr(OPNAME_MULT, LIST_MAKE(createConstInt(3), prodK)));

	//patternIG + coverage + informativeness
	Node *sumOpK = (Node *) (createOpExpr(OPNAME_ADD, inputTopK));

	//3 * (patternIG * coverage * informativeness) / (patternIG + coverage + informativeness)
	Node *fscoreTopK = (Node *) (createOpExpr(OPNAME_DIV, LIST_MAKE(prod3K, sumOpK)));

	// string to float
	CastExpr *cast = createCastExpr(fscoreTopK, DT_FLOAT);

	topKattr = appendToTailOfList(topKattr, cast);
	topKattrNames = appendToTailOfList(topKattrNames, FSCORETOPK);

	//fscoreTopK
	ProjectionOperator *fscoreTopKOp = createProjectionOp(topKattr,
			(QueryOperator *) topKPattConstPlac, NIL, topKattrNames);

	addParent((QueryOperator *) topKPattConstPlac, (QueryOperator *) fscoreTopKOp);
	switchSubtrees((QueryOperator *) topKPattConstPlac, (QueryOperator *) fscoreTopKOp);

	// add projection for order by
	List *oExprs = NIL;
	int oPos = 0;

	FOREACH(AttributeDef, a, fscoreTopKOp->op.schema->attrDefs)
	{
		AttributeReference *ar = createFullAttrReference(a->attrName, 0, oPos, 0, a->dataType);
		oExprs = appendToTailOfList(oExprs, ar);

		oPos++;
	}

	ProjectionOperator *orderPo = createProjectionOp(oExprs,
			(QueryOperator *) fscoreTopKOp, NIL, getAttrNames(fscoreTopKOp->op.schema));

	addParent((QueryOperator *) fscoreTopKOp, (QueryOperator *) orderPo);
	switchSubtrees((QueryOperator *) fscoreTopKOp, (QueryOperator *) orderPo);

	AttributeReference *orderByAr = getAttrRefByName((QueryOperator *) orderPo, FSCORETOPK);
	OrderExpr *ordExpr = createOrderExpr((Node *) orderByAr, SORT_DESC, SORT_NULLS_LAST);
	OrderOperator *fscoreTopKOrderBy = createOrderOp(singleton(ordExpr), (QueryOperator *) orderPo, NIL);

	addParent((QueryOperator *) orderPo, (QueryOperator *) fscoreTopKOrderBy);
	switchSubtrees((QueryOperator *) orderPo, (QueryOperator *) fscoreTopKOrderBy);


	// add LIMIT top-k
	int k = INT_VALUE((Constant *) topk);

	//TODO: postgresql specific
	LimitOperator *fscoreTopKOrderByLimit =
			createLimitOp((Node *) createConstInt(k), NULL, (QueryOperator *) fscoreTopKOrderBy, NIL);

	addParent((QueryOperator *) fscoreTopKOrderBy, (QueryOperator *) fscoreTopKOrderByLimit);
	switchSubtrees((QueryOperator *) fscoreTopKOrderBy, (QueryOperator *) fscoreTopKOrderByLimit);

	INFO_OP_LOG("Top-k patterns that are ordered: ", fscoreTopKOrderByLimit);

	// add a projection to wrap LIMIT
	List *lExprs = NIL;
	int lPos = 0;

	FOREACH(AttributeDef, a, fscoreTopKOp->op.schema->attrDefs)
	{
		AttributeReference *ar = createFullAttrReference(a->attrName, 0, lPos, 0, a->dataType);
		lExprs = appendToTailOfList(lExprs, ar);

		lPos++;
	}

	ProjectionOperator *limitPo = createProjectionOp(lExprs,
			(QueryOperator *) fscoreTopKOrderByLimit, NIL, getAttrNames(fscoreTopKOrderByLimit->op.schema));

	addParent((QueryOperator *) fscoreTopKOrderByLimit, (QueryOperator *) limitPo);
	switchSubtrees((QueryOperator *) fscoreTopKOrderByLimit, (QueryOperator *) limitPo);


	//this needs to be parents of topKPattOnlyConst
	//creating fscoreTopKOnlyCons

	//fscoreTopKOnlyConst
	ProjectionOperator *fscoreTopKOnlyConsOp = createProjectionOp(topKattr,
			(QueryOperator *) topKPattOnlyConst, NIL, topKattrNames);

	addParent((QueryOperator *) topKPattOnlyConst, (QueryOperator *) fscoreTopKOnlyConsOp);
	switchSubtrees((QueryOperator *) topKPattOnlyConst, (QueryOperator *) fscoreTopKOnlyConsOp);

	// add projection for order by
	List *ocoExprs = NIL;
	int ocoPos = 0;

	FOREACH(AttributeDef, a, fscoreTopKOnlyConsOp->op.schema->attrDefs)
	{
		AttributeReference *ar = createFullAttrReference(a->attrName, 0, ocoPos, 0, a->dataType);
		ocoExprs = appendToTailOfList(ocoExprs, ar);

		ocoPos++;
	}

	ProjectionOperator *OcOrderPo = createProjectionOp(ocoExprs,
			(QueryOperator *) fscoreTopKOnlyConsOp, NIL, getAttrNames(fscoreTopKOnlyConsOp->op.schema));

	addParent((QueryOperator *) fscoreTopKOnlyConsOp, (QueryOperator *) OcOrderPo);
	switchSubtrees((QueryOperator *) fscoreTopKOnlyConsOp, (QueryOperator *) OcOrderPo);


	//order by fscoreTopKOnlyConst
	AttributeReference *orderByArOnlyCons = getAttrRefByName((QueryOperator *) OcOrderPo, FSCORETOPK);
	OrderExpr *ordExprOnlyCons = createOrderExpr((Node *) orderByArOnlyCons, SORT_DESC, SORT_NULLS_LAST);
	OrderOperator *fscoreTopKOnlyConsOrderBy =
			createOrderOp(singleton(ordExprOnlyCons), (QueryOperator *) OcOrderPo, NIL);

	addParent((QueryOperator *) OcOrderPo, (QueryOperator *) fscoreTopKOnlyConsOrderBy);
	switchSubtrees((QueryOperator *) OcOrderPo, (QueryOperator *) fscoreTopKOnlyConsOrderBy);

	INFO_OP_LOG("Top-k patterns containing only constants with fscore: ", fscoreTopKOnlyConsOrderBy);


	//creating fscoreTopKOnlyConstSamp
	//creating SELECT MIN(fscoreTopK) FROM fscoreTopK
	//this needs to be parents of fscoreTopK(orderByOp)
	List *minExpr = NIL;
	List *minName = NIL;
	QueryOperator *mQo = (QueryOperator *) copyObject(limitPo);

//	AttributeReference *minAr = createFullAttrReference(FSCORETOPK, 0, topKpos, 0, DT_STRING);
	AttributeReference *minAr = getAttrRefByName((QueryOperator *) limitPo, FSCORETOPK);

	FunctionCall *minf = createFunctionCall("MIN", singleton(minAr));
	minf->isAgg = TRUE;

	minExpr = appendToTailOfList(minExpr, minf);
	minName = appendToTailOfList(minName, MINFSCORETOPK);

//	ProjectionOperator *minfscore = createProjectionOp(minExpr, mQo, NIL, minName);
	AggregationOperator *minfscore = createAggregationOp(minExpr, NIL, mQo, NIL, minName);
	addParent(mQo, (QueryOperator *) minfscore);

	// TODO: make min function attribute float
	FOREACH(AttributeDef, n, minfscore->op.schema->attrDefs)
		n->dataType = DT_FLOAT;


	//creating fscoreTopK > (SELECT MIN(fscoreTopK) FROM fscoreTopK)
	//creating fscoreTopKOnlyConstSamp
	//this needs to be parents of fscoreTopKOnlyConst

	// add an additional projection
	List *projExprs = NIL;
	int arPos = 0;

	FOREACH(AttributeDef, a, minfscore->op.schema->attrDefs)
	{
		AttributeReference *ar = createFullAttrReference(a->attrName, 0, arPos, 0, a->dataType);
		projExprs = appendToTailOfList(projExprs, ar);

		arPos++;
	}

	ProjectionOperator *minfscorePO = createProjectionOp(projExprs,
			(QueryOperator *) minfscore, NIL, getAttrNames(minfscore->op.schema));

	addParent((QueryOperator *) minfscore, (QueryOperator *) minfscorePO);
	switchSubtrees((QueryOperator *) minfscore, (QueryOperator *) minfscorePO);


	// create cross product
	List *inputs = LIST_MAKE(fscoreTopKOnlyConsOrderBy, minfscorePO);
	List *attrNames = CONCAT_LISTS(getAttrNames(fscoreTopKOnlyConsOrderBy->op.schema), singleton(MINFSCORETOPK));

	// create selection comparison min fscore with fscore of patterns with only constants
	// make minfscoretopk from right-side of the join

	QueryOperator *cp = (QueryOperator *) createJoinOp(JOIN_CROSS, NULL, inputs, NIL, attrNames);
	makeAttrNamesUnique((QueryOperator *) cp);

	addParent((QueryOperator *) fscoreTopKOnlyConsOrderBy, (QueryOperator *) cp);
	addParent((QueryOperator *) minfscorePO, (QueryOperator *) cp);

	switchSubtrees((QueryOperator *) fscoreTopKOnlyConsOrderBy, (QueryOperator *) cp);


	// create selection comparison min fscore with fscore of patterns with only constants
	AttributeReference *fscoreTopKar = getAttrRefByName((QueryOperator *) cp, FSCORETOPK);
	AttributeReference *minFscoreTopK =  getAttrRefByName((QueryOperator *) cp, MINFSCORETOPK);
	Node *minCond = (Node *) createOpExpr(OPNAME_GT, LIST_MAKE(fscoreTopKar, minFscoreTopK));
	SelectionOperator *gtmin = createSelectionOp(minCond, (QueryOperator *) cp, NIL, getAttrNames(cp->schema));

	addParent((QueryOperator *) cp, (QueryOperator *) gtmin);
	switchSubtrees((QueryOperator *) cp, (QueryOperator *) gtmin);


	projExprs = NIL;
	arPos = 0;
	List *sampAttrNames = NIL;

	FOREACH(AttributeDef, a, gtmin->op.schema->attrDefs)
	{
		if(!streq(a->attrName, MINFSCORETOPK))
		{
			AttributeReference *ar = createFullAttrReference(a->attrName, 0, arPos, 0, a->dataType);
			projExprs = appendToTailOfList(projExprs, ar);
			sampAttrNames = appendToTailOfList(sampAttrNames, a->attrName);
		}

		arPos++;
	}

	ProjectionOperator *fscoreTopKOnlyConstPo = createProjectionOp(projExprs, (QueryOperator *) gtmin, NIL, sampAttrNames);
	addParent((QueryOperator *) gtmin, (QueryOperator *) fscoreTopKOnlyConstPo);
	switchSubtrees((QueryOperator *) gtmin, (QueryOperator *) fscoreTopKOnlyConstPo);


	// add LIMIT top-k
	//TODO: postgresql specific
	LimitOperator *fscoreTopKOnlyConstSamp = createLimitOp((Node *) createConstInt(k),
			NULL, (QueryOperator *) fscoreTopKOnlyConstPo, NIL);

	addParent((QueryOperator *) fscoreTopKOnlyConstPo, (QueryOperator *) fscoreTopKOnlyConstSamp);
	switchSubtrees((QueryOperator *) fscoreTopKOnlyConstPo, (QueryOperator *) fscoreTopKOnlyConstSamp);

	INFO_OP_LOG("Top-k patterns containing only constants whose fscores are "
			"larger than minimum of fscore of top-k patterns: ", fscoreTopKOnlyConstSamp);

	// add a projection to wrap LIMIT
	lExprs = NIL;
	lPos = 0;

	FOREACH(AttributeDef, a, fscoreTopKOnlyConstSamp->op.schema->attrDefs)
	{
		AttributeReference *ar = createFullAttrReference(a->attrName, 0, lPos, 0, a->dataType);
		lExprs = appendToTailOfList(lExprs, ar);

		lPos++;
	}

	ProjectionOperator *limitPoSamp = createProjectionOp(lExprs,
			(QueryOperator *) fscoreTopKOnlyConstSamp, NIL, getAttrNames(fscoreTopKOnlyConstSamp->op.schema));

	addParent((QueryOperator *) fscoreTopKOnlyConstSamp, (QueryOperator *) limitPoSamp);
	switchSubtrees((QueryOperator *) fscoreTopKOnlyConstSamp, (QueryOperator *) limitPoSamp);


	// UNION top-k patterns
	List *allInput = LIST_MAKE(limitPo, limitPoSamp);
	QueryOperator *unionOp = (QueryOperator *) createSetOperator(SETOP_UNION, allInput,
			NIL, getAttrNames(fscoreTopKOrderByLimit->op.schema));

	addParent((QueryOperator *) limitPo, (QueryOperator *) unionOp);
	addParent((QueryOperator *) limitPoSamp, (QueryOperator *) unionOp);

	switchSubtrees((QueryOperator *) limitPo, unionOp);

//
//-----------------------------------------------------------------
//
	List *JoinAttrNames = NIL;
	List *joinList = NIL;
	Node *joinCondt = NULL;


// for new unionOp is topK
	FOREACH(AttributeDef, L, unionOp->schema->attrDefs)
	{
		FOREACH(AttributeDef, R, clean->op.schema->attrDefs)
		{
			if(streq(L->attrName, R->attrName))
			{
				AttributeReference *arL = createFullAttrReference(L->attrName, 0,
							getAttrPos((QueryOperator *) unionOp, L->attrName), 0, L->dataType);
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

	joinCondt = (Node *) createOpExpr(OPNAME_AND, joinList);

	QueryOperator *copyClean = copyObject(clean);
	List *allInputJoin = LIST_MAKE((QueryOperator *) unionOp, copyClean);
	JoinAttrNames = CONCAT_LISTS(getAttrNames(unionOp->schema), getAttrNames(clean->op.schema));
	QueryOperator *joinOp = (QueryOperator *) createJoinOp(JOIN_INNER, joinCondt, allInputJoin, NIL, JoinAttrNames);

	makeAttrNamesUnique((QueryOperator *) joinOp);
	SET_BOOL_STRING_PROP(joinOp, PROP_MATERIALIZE);

	addParent(copyClean, joinOp);
	addParent((QueryOperator *) unionOp, joinOp);

	switchSubtrees((QueryOperator *) unionOp, (QueryOperator *) joinOp);
	DEBUG_NODE_BEATIFY_LOG("Join Patterns with Data: ", joinOp);


	// Add projection to exclude unnecessary attributes
	List *projExprsClean = NIL;
	List *attrNamesClean = NIL;
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


	FOREACH(AttributeDef, a, joinOp->schema->attrDefs)
	{
		if(!searchListNode(unNecAttr,(Node *) a))
		{
			AttributeReference *ar = createFullAttrReference(a->attrName, 0,
				getAttrPos((QueryOperator *) joinOp, a->attrName), 0, a->dataType);

			projExprsClean = appendToTailOfList(projExprsClean,ar);
			attrNamesClean = appendToTailOfList(attrNamesClean,ar->name);
		}
	}

	ProjectionOperator *po = createProjectionOp(projExprsClean, NULL, NIL, attrNamesClean);
	addChildOperator((QueryOperator *) po, (QueryOperator *) joinOp);
	switchSubtrees((QueryOperator *) joinOp, (QueryOperator *) po);
	SET_BOOL_STRING_PROP(po, PROP_MATERIALIZE);

	// Adding duplicate elimination
	projExprsClean = NIL;
	List *attrDefs = po->op.schema->attrDefs;

	FOREACH(AttributeDef, a, attrDefs)
	{
		AttributeReference *ar = createFullAttrReference(a->attrName, 0,
			getAttrPos((QueryOperator *) po, a->attrName), 0, a->dataType);

		projExprsClean = appendToTailOfList(projExprsClean,ar);
	}

	QueryOperator *dr = (QueryOperator *) createDuplicateRemovalOp(projExprsClean, (QueryOperator *) po, NIL, getAttrDefNames(attrDefs));
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
			Node *input = (Node *) createOpExpr("+", LIST_MAKE(createConstInt(1), coalesce));
			aggrsAnalysis = appendToTailOfList(aggrsAnalysis, input);
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

    // store the join query
    if(HAS_STRING_PROP(OP_LCHILD(op), PROP_JOIN_OP_IG))
	{
		SET_STRING_PROP(OP_LCHILD(op), PROP_JOIN_OP_IG,
				copyObject(GET_STRING_PROP(OP_LCHILD(op), PROP_JOIN_OP_IG)));
	}
    else
    	SET_STRING_PROP(op, PROP_JOIN_OP_IG, OP_LCHILD(op));


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


    QueryOperator *child = OP_LCHILD(op);

    // rewrite child
    rewriteIG_Operator(child);

    //TODO: op should be expanded to have ig columns.

	// Getting Table name and length of table name here
	char *tblNameL = "";
	HashMap *attrLNames = NEW_MAP(Constant, Node);
	HashMap *attrRNames = NEW_MAP(Constant, Node);

    List *joinCond = (List *) GET_STRING_PROP(child, PROP_JOIN_ATTRS_FOR_HAMMING);
    List *joinAttrs = NIL;

    FOREACH(Operator, o, joinCond)
    {
    	FOREACH(AttributeReference, ar, o->args)
		{
    		joinAttrs = appendToTailOfList(joinAttrs, ar->name);
		}
    }

    FOREACH(AttributeDef, n, attrL)
	{
		if(isPrefix(n->attrName, IG_PREFIX))
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
		if(isPrefix(n->attrName, IG_PREFIX))
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

					if(isA(n, AttributeReference))
					{
						FOREACH(AttributeReference, ar, whenArgs)
						{
							ar->attrPosition = getAttrPos((QueryOperator *) child,ar->name);
						}
					}
				}

				// then
				AttributeReference *then = (AttributeReference *) cw->then;
				then->attrPosition = getAttrPos((QueryOperator *) child, then->name);
			}

			// else
			AttributeReference *els = (AttributeReference *) ce->elseRes;
			els->attrPosition = getAttrPos((QueryOperator *) child, els->name);

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
		if(!isA(n, CaseExpr) && !isA(n, Operator))
		{
			AttributeReference *ar = (AttributeReference *) n;
			if(MAP_HAS_STRING_KEY(attrLNames, ar->name) &&
					MAP_HAS_STRING_KEY(attrRNames, ar->name))
			{
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
			FunctionCall *coalesce = NULL;

			if(isA(n,CaseExpr))
			{
				CaseExpr *ce = (CaseExpr *) n;
				AttributeReference *els = (AttributeReference *) ce->elseRes;

				if(els->attrType == DT_STRING || els->attrType == DT_VARCHAR2)
					coalesce = createFunctionCall("COALESCE", LIST_MAKE(n, (Node *) createConstString("na")));

				if(els->attrType == DT_INT || els->attrType == DT_FLOAT || els->attrType == DT_LONG)
					coalesce = createFunctionCall("COALESCE", LIST_MAKE(n, (Node *) createConstInt(0)));
			}
			else
			{
				FATAL_LOG("!! Under Construction !!");
			}

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

    // add additional ig columns
    List *addIgExprs = NIL;
    List *addIgAttrs = NIL;

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

    // adding ig attribute after the integration
    FOREACH(Node, n, op->projExprs)
    {
    	if(!isA(n, CaseExpr))
    	{
    		AttributeReference *ar = (AttributeReference *) n;

    		//TODO: remove unique number in the attr from shared
    		char *origAttrName = ar->name;

    		char *igName = CONCAT_STRINGS("ig_conv_",
    									MAP_HAS_STRING_KEY(attrLNames, origAttrName) ? tblNameL : tblNameR, origAttrName);

    		char *attrNameAfterReplace = replaceSubstr(ar->name,gprom_itoa(1),"");
    		igName = replaceSubstr(igName, origAttrName, attrNameAfterReplace);

    		if(MAP_HAS_STRING_KEY(igAttrs, igName))
    		{
    			AttributeReference *igExpr = (AttributeReference *) MAP_GET_STRING(igAttrs, igName);
    			AttributeReference *ar = createFullAttrReference(igExpr->name, 0, igExpr->attrPosition, 0, igExpr->attrType);

    			addIgExprs = appendToTailOfList(addIgExprs, ar);
    			addIgAttrs = appendToTailOfList(addIgAttrs, CONCAT_STRINGS(igName,INTEG_SUFFIX));
    		}

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
			char *origAttrName = ar->name;

			igName = CONCAT_STRINGS("ig_conv_",
										MAP_HAS_STRING_KEY(attrLNames, origAttrName) ? tblNameL : tblNameR,
												origAttrName);

    		char *attrNameAfterReplace = replaceSubstr(ar->name,gprom_itoa(1),"");
    		igName = replaceSubstr(igName, origAttrName, attrNameAfterReplace);

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

    // store the join query
	SET_STRING_PROP(newProj, PROP_JOIN_OP_IG,
			copyObject(GET_STRING_PROP(op, PROP_JOIN_OP_IG)));

    INFO_OP_LOG("Rewritten Operator tree for all IG attributes", newProj);

//  This function creates hash maps and adds hamming distance functions
	ProjectionOperator *hammingvalue_op = rewriteIG_HammingFunctions(newProj);

//	This function adds the + expression to calculate the total distance
	ProjectionOperator *sumrows = rewriteIG_SumExprs(hammingvalue_op);

	if(explFlag == FALSE)
	{

		INFO_OP_LOG("Rewritten Operator tree for patterns", (QueryOperator *) sumrows);
		return (QueryOperator *) sumrows;
	}
	else
	{
		AggregationOperator *patterns = rewriteIG_PatternGeneration(sumrows);

		QueryOperator *analysis = rewriteIG_Analysis(patterns);

		INFO_OP_LOG("Rewritten Operator tree for patterns", (QueryOperator *) analysis);
		return (QueryOperator *) analysis;
	}


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
