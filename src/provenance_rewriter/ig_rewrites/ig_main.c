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
static ProvenanceType provType;


QueryOperator *
rewriteIG (ProvenanceComputation  *op)
{
	// IG
	provType = op->provType;

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
    return rewrittenOp;
}


static QueryOperator *
rewriteIG_Conversion (ProjectionOperator *op)
{
	List *newProjExprs = NIL;
	List *attrNames = NIL;

	FOREACH(AttributeReference, a, op->projExprs)
	{
		if(isPrefix(a->name,"ig"))
		{
//			AttributeReference *ar = getAttrRefByName((QueryOperator *) op, a->attrName);

//			if(a->attrType == DT_INT || a->attrType == DT_FLOAT)
//			{
//				CastExpr *cast;
//				cast = createCastExpr((Node *) a, DT_FLOAT);  // change to bit10
//				newProjExprs = appendToTailOfList(newProjExprs, cast);
//			}
//			else
			if (a->attrType == DT_STRING)
			{
				StringToArray *toArray;
				Unnest *tounnest;
				Ascii *toAscii;
//					Sum *toSum;

				toArray = createStringToArrayExpr((Node *) a, "NULL");
				tounnest = createUnnestExpr((Node *) toArray);
				toAscii = createAsciiExpr((Node *) tounnest);
//					toSum = createSumExpr((Node *) toAscii);

				newProjExprs = appendToTailOfList(newProjExprs, toAscii);
			}
			else
			{
				newProjExprs = appendToTailOfList(newProjExprs, a);
			}
		}
		else
		{
//			AttributeReference *ar = getAttrRefByName((QueryOperator *) op, a->attrName);
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

	// Creating aggregate operation
//	QueryOperator *o = copyObject((QueryOperator *) op);
	List *aggrs = NIL;
	List *groupBy = NIL;
	attrNames = NIL;

	int i = 0;
//	int ai = 0;
//	int gi = 0;


	FOREACH(Node,n,newProjExprs)
	{
		if(isA(n,Ascii))
		{
			char *attrName = getAttrNameByPos((QueryOperator *) po, i);
			AttributeReference *ar = createAttrsRefByName((QueryOperator *) po, attrName);
			FunctionCall *sum = createFunctionCall("SUM", singleton(ar));
			aggrs = appendToTailOfList(aggrs,sum);

//			attrNames = appendToTailOfList(attrNames, CONCAT_STRINGS("AGGR_", gprom_itoa(ai)));
//			ai++;
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

//			attrNames = appendToTailOfList(attrNames, CONCAT_STRINGS("GROUP_", gprom_itoa(gi)));
//			gi++;
		}

		i++;
	}

//	//create fake attribute names for aggregation output schema
	for (i = 0; i < LIST_LENGTH(aggrs); i++)
		attrNames = appendToTailOfList(attrNames, CONCAT_STRINGS("AGGR_", gprom_itoa(i)));
	for (i = 0; i < LIST_LENGTH(groupBy); i++)
		attrNames = appendToTailOfList(attrNames, CONCAT_STRINGS("GROUP_", gprom_itoa(i)));

	AggregationOperator *ao = createAggregationOp(aggrs, groupBy, NULL, NIL, attrNames);
	addChildOperator((QueryOperator *) ao, (QueryOperator *) po);

// Switch the subtree with this newly created projection operator.
	switchSubtrees((QueryOperator *) po, (QueryOperator *) ao);

	LOG_RESULT("Rewritten Aggregation Operator tree", ao);

	// CREATING THE NEW PROJECTION OPERATOR
//	projExprs = concatTwoLists(ao->aggrs, ao->groupBy);

	projExprs = NIL;
	cnt = 0;
//	List *attrs = NIL;
//	QueryOperator *child = OP_LCHILD(ao);

	FOREACH(AttributeDef,a,ao->op.schema->attrDefs)
	{
//		projExprs = appendToTailOfList(projExprs,
//				getAttrRefByPos(child, cnt));

//		AttributeDef *att = getAttrDef(child, cnt);
		projExprs = appendToTailOfList(projExprs,
				createFullAttrReference(a->attrName, 0, cnt, 0, a->dataType));
		cnt++;
	}

	//create projection operator upon selection operator from select clause
	ProjectionOperator *newPo = createProjectionOp(projExprs, NULL, NIL, attrNames);
	addChildOperator((QueryOperator *) newPo, (QueryOperator *) ao);

	// Switch the subtree with this newly created projection operator.
	switchSubtrees((QueryOperator *) ao, (QueryOperator *) newPo);

	// CAST_EXPR
	newProjExprs = NIL;

	FOREACH(AttributeReference, a, newPo->projExprs)
	{
		if(a->attrType == DT_INT || a->attrType == DT_FLOAT)
		{
			CastExpr *cast;
			cast = createCastExpr((Node *) a, DT_FLOAT);  // change to bit10
			newProjExprs = appendToTailOfList(newProjExprs, cast);
		}
		else
			newProjExprs = appendToTailOfList(newProjExprs, a);
	}

	newPo->projExprs = newProjExprs;

    LOG_RESULT("Converted Operator tree", newPo);
	return (QueryOperator *) newPo;
}


static QueryOperator *
rewriteIG_Projection (ProjectionOperator *op)
{

    ASSERT(OP_LCHILD(op));
    DEBUG_LOG("IG - Projection");
    DEBUG_LOG("Operator tree \n%s", nodeToString(op));

    // rewrite child
    rewriteIG_Operator(OP_LCHILD(op));

//    // add projection expressions for ig attrs
//    QueryOperator *child = OP_LCHILD(op);
//    LOG_RESULT("Query operator child", child);
//
//    FOREACH_INT(a, child->igAttrs)
//    {
//        AttributeDef *att = getAttrDef(child,a);
//        op->projExprs = appendToTailOfList(op->projExprs,
//                 createFullAttrReference(att->attrName, 0, a, 0, att->dataType));
//    }
//
//    // adapt schema
//    addIGAttrsToSchema((QueryOperator *) op, OP_LCHILD(op));

    //TODO: Implement queryIntegration

//    //TODO: temporary test to return aggregate result. remove while implementing queryIntegration
    QueryOperator *child = OP_LCHILD(op);
//    if(isA(child,AggregationOperator)) {
	switchSubtrees((QueryOperator *) op, (QueryOperator *) child);
//    }

    LOG_RESULT("Rewritten Projection Operator tree", op);
    return (QueryOperator *) op;
}

static QueryOperator *
rewriteIG_Join (JoinOperator *op)
{
    DEBUG_LOG("IG - Join");

    QueryOperator *o = (QueryOperator *) op;
    QueryOperator *lChild = OP_LCHILD(op);
    QueryOperator *rChild = OP_RCHILD(op);

    lChild = rewriteIG_Operator(lChild);
    rChild = rewriteIG_Operator(rChild);

    addChildOperator(o, lChild);
    addChildOperator(o, rChild);

    // add projection to put attributes into order on top of join op
    List *projExpr = getNormalAttrProjectionExprs((QueryOperator *) o);
    ProjectionOperator *proj = createProjectionOp(projExpr, NULL, NIL, NIL);
    addChildOperator((QueryOperator *) proj, (QueryOperator *) op);

    LOG_RESULT("Rewritten IG Operator tree", proj);
    return (QueryOperator *) proj;
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
