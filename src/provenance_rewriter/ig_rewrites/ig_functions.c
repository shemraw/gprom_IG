/*
 *
 * A FILE FOR IG FUNCTIONS SO IN THIS CASE
 *
 */

#include "provenance_rewriter/ig_rewrites/ig_main.h"
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

//typedef struct AsciiAggrs {
//    List *aggrNames;
//    List *groupBy;
//    List *aggrs;
//} AsciiAggrs;
//


//function for testing only
extern QueryOperator *rewriteIG_test(QueryOperator *);

//Input : AttributeReference (Data Type : DT_STRING)
//Pitput : array of Ascii codes of string (Data Type : DT_INT)
extern Ascii *convertArtoAscii(AttributeReference *);


//Input : ProjectionOperator
//Output : List of converted AttributeReference toAscii and rest of the attributes
extern List *toAsciiList(ProjectionOperator *);


//Input : List of projection expressions(contains Ascii, AttributeReference, CastExpr)
extern List *getAsciiAggrs(List *, ProjectionOperator *);

QueryOperator *rewriteIG_test(QueryOperator *input)
{
	return input;
}

Ascii *convertArtoAscii(AttributeReference *a)
{
	StringToArray *toArray;
	Unnest *tounnest;
	Ascii *toAscii;

	if (a->attrType == DT_STRING)
	{
		toArray = createStringToArrayExpr((Node *) a, "NULL");
		tounnest = createUnnestExpr((Node *) toArray);
		toAscii = createAsciiExpr((Node *) tounnest);
	}
	else
	{
		// invalid input : ERROR
		return NULL;
	}

	return toAscii;
}

List *toAsciiList(ProjectionOperator *op)
{
	List *projExprs = NIL;

	FOREACH(AttributeReference, a, op->projExprs)
	{
		if(isPrefix(a->name,"ig"))
		{
			if (a->attrType == DT_STRING)
			{
				Ascii *toAscii = convertArtoAscii(a);
				projExprs = appendToTailOfList(projExprs, toAscii);
			}
			else
			{
				projExprs = appendToTailOfList(projExprs, a);
			}
		}
		else
		{
			projExprs = appendToTailOfList(projExprs, a);
		}
	}

	return projExprs;
}

//
//AsciiAggrs *getAsciiAggrs(List *projExprs, ProjectionOperator *po)
//{
//	AsciiAggrs *a = NULL;
//	List *aggrs = NIL;
//	List *groupBy = NIL;
//	List *newNames = NIL;
//	List *aggrNames = NIL;
//	List *groupByNames = NIL;
//	int i = 0;
//
//	FOREACH(Node,n,projExprs)
//	{
//		if(isA(n,Ascii))
//		{
//			char *attrName = getAttrNameByPos((QueryOperator *) po, i);
//			AttributeReference *ar = createAttrsRefByName((QueryOperator *) po, attrName);
//			FunctionCall *sum = createFunctionCall("SUM", singleton(ar));
//			aggrs = appendToTailOfList(aggrs,sum);
//			aggrNames = appendToTailOfList(aggrNames,attrName);
//		}
//		else
//		{
//			if(isA(n,AttributeReference))
//			{
//				groupBy = appendToTailOfList(groupBy,n);
//
//				AttributeReference *ar = (AttributeReference *) n;
//				groupByNames = appendToTailOfList(groupByNames,(ar->name));
//			}
//
//			if(isA(n,CastExpr))
//			{
//				CastExpr *ce = (CastExpr *) n;
//				AttributeReference *ar = (AttributeReference *) ce->expr;
//				groupBy = appendToTailOfList(groupBy, (Node *) ar);
//			}
//		}
//
//		i++;
//	}
//
//	newNames = CONCAT_LISTS(aggrNames, groupByNames);
//
//	a->aggrs = aggrs;
//	a->groupBy = groupBy;
//	a->aggrNames = newNames;
//
//	return a;
//
//}


// test function
List *getAsciiAggrs(List *projExprs, ProjectionOperator *po)
{
	List *aggrs = NIL;
	int i = 0;

	FOREACH(Node,n,projExprs)
	{
		if(isA(n,Ascii))
		{
			char *attrName = getAttrNameByPos((QueryOperator *) po, i);
			AttributeReference *ar = createAttrsRefByName((QueryOperator *) po, attrName);
			FunctionCall *sum = createFunctionCall("SUM", singleton(ar));
			aggrs = appendToTailOfList(aggrs,sum);
		}

		i++;
	}
	return aggrs;
}


