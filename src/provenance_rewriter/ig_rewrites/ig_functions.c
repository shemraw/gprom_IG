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

#define IG_PREFIX "ig_"

// creates a list of attribute references from a list of attributeDefs with no given positions
extern List *getARfromAttrDefs(List *qo);
extern List *getNamesfromAttrDefs(List *qo);
extern List *getARfromAttrDefswPos(QueryOperator *qo, List *attrDefs);
extern char *getTableNamefromPo(ProjectionOperator *po);
extern List *getARfromPoAr(ProjectionOperator *po);
extern List *getNamesfromPoAr(ProjectionOperator *po);


//Input : AttributeReference (Data Type : DT_STRING)
//Pitput : array of Ascii codes of string (Data Type : DT_INT)
extern Ascii *convertArtoAscii(AttributeReference *ar);

//Input : ProjectionOperator
//Output : List of converted AttributeReference toAscii and rest of the attributes
extern List *toAsciiList(ProjectionOperator *po);

//Input : List of projection expressions(contains Ascii, AttributeReference, CastExpr)
extern List *getAsciiAggrs(List *projExprs, ProjectionOperator *po);



//rewrite conversion functions

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

// creates a list of attribute references from a list of attributeDefs with no given positions
List *getARfromAttrDefs(List *attrDefs)
{
	List *projExprs = NIL;
	int pos = 0;

	FOREACH(AttributeDef, a, attrDefs)
	{

		projExprs = appendToTailOfList(projExprs,
				createFullAttrReference(a->attrName, 0, pos, 0, a->dataType));

		pos++;
	}

	return projExprs;
}

// creates a list of attribute references from a list of attributeDefs with given positions form an expression
List *getARfromAttrDefswPos(QueryOperator *qo, List *attrDefs)
{
	List *projExprs = NIL;

	FOREACH(AttributeDef, a, attrDefs)
	{
		projExprs = appendToTailOfList(projExprs,
			createFullAttrReference(a->attrName, 0,
					getAttrPos(qo, a->attrName), 0,
					isPrefix(a->attrName,"ig") ? DT_BIT10 : a->dataType));

	}

	return projExprs;
}


List *getNamesfromAttrDefs(List *attrDefs)
{
	List *projNames = NIL;
	FOREACH(AttributeDef, a, attrDefs)
	{
		projNames = appendToTailOfList(projNames, a->attrName);
	}

	return projNames;
}

char *getTableNamefromPo(ProjectionOperator *po)
{
	char *tableName = NULL;
	FOREACH(AttributeReference, n, po->projExprs)
	{
		if(isPrefix(n->name, IG_PREFIX))
		{
			int len1 = strlen(n->name);
			int len2 = strlen(strrchr(n->name, '_'));
			int len = len1 - len2 - 1;
			tableName = substr(n->name, 8, len);
		}
	}
	return tableName;
}

List *getARfromPoAr(ProjectionOperator *po)
{
	List *projExprs = NIL;
	FOREACH(AttributeReference, n, po->projExprs)
	{
		projExprs = appendToTailOfList(projExprs, n);
	}
	return projExprs;
}

List *getNamesfromPoAr(ProjectionOperator *po)
{
	List *projNames = NIL;
	FOREACH(AttributeReference, n, po->projExprs)
	{
		projNames = appendToTailOfList(projNames, n->name);
	}
	return projNames;
}



