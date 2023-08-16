/*
 *
 * A FILE FOR IG FUNCTIONS SO IN THIS CASE
 * rewriteIG_SumExprs and rewriteIG_HammingFunctions
 *
 */

//
//#include "src/provenance_rewriter/ig_rewrites/ig_main.c"

//static ProjectionOperator *rewriteIG_SumExprs(ProjectionOperator *op);
//static ProjectionOperator *rewriteIG_HammingFunctions(ProjectionOperator *op);


/*

//rewriteIG_SumExprs
static ProjectionOperator *
rewriteIG_SumExprs (ProjectionOperator *hammingvalue_op)
{
    ASSERT(OP_LCHILD(hammingvalue_op));
    DEBUG_LOG("REWRITE-IG - Projection");
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
		if(isPrefix(a->attrName, "value"))
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
	sumNames = appendToTailOfList(sumNames, "Total_Distance");

	// Just tesing Average Expression Just in Case if we need it later in future
	avgExpr = (Node *) (createOpExpr("/", LIST_MAKE(createOpExpr("+", sumlist), createConstInt(3))));
	sumExprs = appendToTailOfList(sumExprs, avgExpr);
	sumNames = appendToTailOfList(sumNames, "Average_Distance");

	ProjectionOperator *sumrows = createProjectionOp(sumExprs, NULL, NIL, sumNames);
	//LOG_RESULT("TESTING SUM_AVG_ROWS FUNCTION", sumrows);

	addChildOperator((QueryOperator *) sumrows, (QueryOperator *) hammingvalue_op);
	switchSubtrees((QueryOperator *) hammingvalue_op, (QueryOperator *) sumrows);

	return sumrows;

}

*/

/*
//rewriteIG_HammingFunctions

static ProjectionOperator *
rewriteIG_HammingFunctions (ProjectionOperator *newProj)
{
    ASSERT(OP_LCHILD(newProj));
    DEBUG_LOG("REWRITE-IG - Projection");
    DEBUG_LOG("Operator tree \n%s", nodeToString(newProj));

    // Creating the HASH MAPS
    List *newProjExpr = NIL;
    int lenL = LIST_LENGTH(attrL) - 1;
    int l = 0;
    int posOfIgL = LIST_LENGTH(attrL) / 2;
    int posOfIgR = LIST_LENGTH(attrR) / 2;

    List *LprojExprs = NIL;
    List *RprojExprs = NIL;
    List *LattrNames = NIL;
    List *RattrNames = NIL;
    List* joinAttrs = NIL;

    //joinAttrs = (List *) GET_STRING_PROP(newProj, PROP_JOIN_ATTRS_FOR_HAMMING);

    HashMap *nameToIgAttrNameL = NEW_MAP(Constant, Constant);
    HashMap *nameToIgAttrNameR = NEW_MAP(Constant, Constant);


    FOREACH(AttributeDef,a,attrL)
    {
		if(!isPrefix(a->attrName,"ig"))
		{
			char *key = a->attrName;
			AttributeDef *igA = (AttributeDef *) getNthOfListP(attrL, posOfIgL);
			char *value = igA->attrName;

			ADD_TO_MAP(nameToIgAttrNameL,createStringKeyValue(key,value));
			posOfIgL++;
		}
		else if(isSuffix(a->attrName,"anno"))
		{
			char *kv = a->attrName;
			ADD_TO_MAP(nameToIgAttrNameL,createStringKeyValue(kv,kv));
			posOfIgL++;
		}
    }

    FOREACH(AttributeDef,a,attrR)
	{
		if(!isPrefix(a->attrName,"ig"))
		{
			char *key = a->attrName;
			AttributeDef *igA = (AttributeDef *) getNthOfListP(attrR,posOfIgR);
			char *value = igA->attrName;

			ADD_TO_MAP(nameToIgAttrNameR,createStringKeyValue(key,value));
			posOfIgR++;
		}
		else if(isSuffix(a->attrName,"anno"))
		{
			char *kv = a->attrName;
			ADD_TO_MAP(nameToIgAttrNameR,createStringKeyValue(kv,kv));
			posOfIgR++;
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


	FOREACH(AttributeReference, n, LprojExprs)
	{
		if(!isPrefix(n->name, "ig") && !isSuffix(n->name, "anno"))
		{
			newProjExpr = appendToTailOfList(newProjExpr, n);
		}

	}


	FOREACH(AttributeReference, n, LprojExprs)
	{
		if(!isPrefix(n->name, "ig") && !isSuffix(n->name, "anno"))
		{
			if(MAP_HAS_STRING_KEY(nameToIgAttrNameR, n->name))
			{
				char *attrIgNameL = STRING_VALUE(MAP_GET_STRING(nameToIgAttrNameL, n->name));
				char *attrIgNameR = STRING_VALUE(MAP_GET_STRING(nameToIgAttrNameR, n->name));

				AttributeReference *ar = createFullAttrReference(attrIgNameL, 0,
						listPosString(LattrNames,attrIgNameL), 0, DT_BIT15);
				Node *cond = (Node *) createIsNullExpr((Node *) ar);
				Node *then = (Node *) createFullAttrReference(attrIgNameR, 0,
						LIST_LENGTH(LattrNames) + listPosString(RattrNames,attrIgNameR),
						0, DT_BIT15);
				Node *els = (Node *) ar;

				CaseWhen *caseWhen = createCaseWhen(cond, then);
				CaseExpr *caseExpr = createCaseExpr(NULL, singleton(caseWhen), els);

				newProjExpr = appendToTailOfList(newProjExpr, caseExpr);
			}
			else
			{
				char *igAttr = STRING_VALUE(MAP_GET_STRING(nameToIgAttrNameL, n->name));
				AttributeReference *ar = createFullAttrReference(igAttr, 0,
						listPosString(LattrNames,igAttr), 0, DT_BIT15);
				newProjExpr = appendToTailOfList(newProjExpr, ar);
			}
		}

		if(isSuffix(n->name, "anno"))
			newProjExpr = appendToTailOfList(newProjExpr, n);
	}


	FOREACH(AttributeReference, n, RprojExprs)
	{
		if(!isPrefix(n->name, "ig") && !isSuffix(n->name, "anno"))
		{
			newProjExpr = appendToTailOfList(newProjExpr, n);
		}

	}

	// TODO : ERROR IN THIS LOOP FIX IT TO SUPPORT NEW CASE WHEN
	FOREACH(AttributeReference, n, RprojExprs)
	{
		if(!isPrefix(n->name, "ig") && !isSuffix(n->name, "anno"))
		{
			char *ch = replaceSubstr(n->name, "1", "");

			if(MAP_HAS_STRING_KEY(nameToIgAttrNameL, ch))
			{
				char *attrIgNameL = STRING_VALUE(MAP_GET_STRING(nameToIgAttrNameL, ch));
				char *attrIgNameR = STRING_VALUE(MAP_GET_STRING(nameToIgAttrNameR, ch));

				AttributeReference *ar = createFullAttrReference(attrIgNameR, 0,
						LIST_LENGTH(LattrNames) + listPosString(RattrNames,attrIgNameR),
						0, DT_BIT15);
				Node *cond = (Node *) createIsNullExpr((Node *) ar);
				Node *then = (Node *) createFullAttrReference(attrIgNameL, 0,
						listPosString(LattrNames,attrIgNameL), 0, DT_BIT15);
				Node *els  = (Node *) ar;

				CaseWhen *caseWhen = createCaseWhen(cond, then);
				CaseExpr *caseExpr = createCaseExpr(NULL, singleton(caseWhen), els);

				newProjExpr = appendToTailOfList(newProjExpr, caseExpr);
			}
			else
			{
				char *igAttr = STRING_VALUE(MAP_GET_STRING(nameToIgAttrNameR, ch));
				AttributeReference *ar = createFullAttrReference(igAttr, 0,
										 listPosString(RattrNames,igAttr) + lenL + 1, 0, DT_BIT15);
				newProjExpr = appendToTailOfList(newProjExpr, ar);
			}
		}

		if(isSuffix(n->name, "anno"))
			newProjExpr = appendToTailOfList(newProjExpr, n);
	}

	List *attrNames = CONCAT_LISTS(LattrNames,RattrNames);
    ProjectionOperator *op1 = createProjectionOp(newProjExpr, NULL, NIL, attrNames);

    addChildOperator((QueryOperator *) op1, (QueryOperator *) newProj);
    switchSubtrees((QueryOperator *) newProj, (QueryOperator *) op1);

    // Adding hammingDist function
    List *exprs = NIL;
    List *atNames = NIL;
    int x = 0;



    FOREACH(AttributeDef, a, op1->op.schema->attrDefs)
	{

    	if(isPrefix(a->attrName, "ig"))
    	{
    		AttributeReference *ar = createFullAttrReference(a->attrName, 0, x, 0, DT_BIT15);
			exprs = appendToTailOfList(exprs, ar);
			atNames = appendToTailOfList(atNames, a->attrName);
			x++;
    	}
    	else
    	{
    		AttributeReference *ar = createFullAttrReference(a->attrName, 0, x, 0, a->dataType);
			exprs = appendToTailOfList(exprs, ar);
			atNames = appendToTailOfList(atNames, a->attrName);
			x++;
    	}

	}

	// for the join attributes
	List *functioninput = NIL;
	char *tempName = NULL;
	joinAttrs = (List *) GET_STRING_PROP(newProj, PROP_JOIN_ATTRS_FOR_HAMMING);
	int cnt = 0;

	FOREACH(AttributeReference, n, joinAttrs)
	{

		//GETS THE JOIN ATTRIBUTE FROM FIRST TABLE
		if(n->fromClauseItem == 0)
		{
			if(MAP_HAS_STRING_KEY(nameToIgAttrNameL, n->name))
			{
				char *attrName = STRING_VALUE(MAP_GET_STRING(nameToIgAttrNameL, n->name));
				AttributeReference *ar = createFullAttrReference(attrName, 0,
										listPosString(LattrNames,attrName), 0,
										isPrefix(attrName,"ig") ? DT_BIT15 : n->attrType);

				CastExpr *castL;
				castL = createCastExpr((Node *) ar, DT_STRING);
				functioninput = appendToTailOfList(functioninput, castL);
				tempName = n->name;
				cnt ++;
			}
		}

		//GETS THE JOIN ATTRIBUTE FROM SECOND TABLE
		if(n->fromClauseItem == 1)
		{
			if(MAP_HAS_STRING_KEY(nameToIgAttrNameR, n->name))
			{
				char *attrName = STRING_VALUE(MAP_GET_STRING(nameToIgAttrNameR, n->name));
				AttributeReference *ar = createFullAttrReference(attrName, 0,
						LIST_LENGTH(LattrNames) + listPosString(RattrNames,attrName) - (lenL + 1),
						0, isPrefix(attrName,"ig") ? DT_BIT15 : n->attrType);

				CastExpr *castR;
				castR = createCastExpr((Node *) ar, DT_STRING);
				functioninput = appendToTailOfList(functioninput, castR);
				cnt ++;
			}
		}

		if(cnt == 2)
		{
			atNames = appendToTailOfList(atNames, CONCAT_STRINGS("hamming_", tempName));
			FunctionCall *hammingdist = createFunctionCall("hammingdist", functioninput);
			exprs = appendToTailOfList(exprs,hammingdist);
			functioninput = NIL;
			cnt = 0;
		}

	}

	List *joinNames = NIL;
	FOREACH(AttributeReference, n, joinAttrs)
	{
		joinNames = appendToTailOfList(joinNames, n->name);
	}

	FOREACH(AttributeReference, n, LprojExprs)
	{
		List *functioninput = NIL;
		List *cast = NIL;

		boolean flag = searchListString(joinNames, n->name);

		if(!isPrefix(n->name, "ig") && flag == FALSE)
		{
			if(MAP_HAS_STRING_KEY(nameToIgAttrNameR, n->name) && !isSuffix(n->name, "anno"))
			{
				char *attrIgNameL = STRING_VALUE(MAP_GET_STRING(nameToIgAttrNameL, n->name));
				char *attrIgNameR = STRING_VALUE(MAP_GET_STRING(nameToIgAttrNameR, n->name));

				AttributeReference *arL = createFullAttrReference(attrIgNameL, 0,
						listPosString(LattrNames,attrIgNameL), 0,
						isPrefix(attrIgNameL,"ig") ? DT_BIT15 : n->attrType);

				AttributeReference *arR = createFullAttrReference(attrIgNameR, 0,
						LIST_LENGTH(LattrNames) + listPosString(RattrNames,attrIgNameR) - (lenL + 1),
						0, isPrefix(attrIgNameR,"ig") ? DT_BIT15 : n->attrType);

				CastExpr *castL;
				CastExpr *castR;

				castL = createCastExpr((Node *) arL, DT_STRING);
				castR = createCastExpr((Node *) arR, DT_STRING);

				cast = appendToTailOfList(cast, castL);
				cast = appendToTailOfList(cast, castR);

				functioninput = appendToTailOfList(functioninput, arL);
				functioninput = appendToTailOfList(functioninput, arR);

				FunctionCall *hammingdist = createFunctionCall("hammingdist", cast);
				Node *cond = (Node *)(createOpExpr("=",functioninput));
				Node *then = (Node *)(createConstString("000000000000000"));
				Node *els  = (Node *) hammingdist;
				CaseWhen *caseWhen = createCaseWhen(cond, then);
				CaseExpr *caseExpr = createCaseExpr(NULL, singleton(caseWhen), els);

				exprs = appendToTailOfList(exprs,caseExpr);
				atNames = appendToTailOfList(atNames, CONCAT_STRINGS("hamming_", n->name));
				x++;

			}
			else if(!MAP_HAS_STRING_KEY(nameToIgAttrNameR, n->name) && !isSuffix(n->name, "anno"))
			{
				char *attrIgNameL = STRING_VALUE(MAP_GET_STRING(nameToIgAttrNameL, n->name));

				AttributeReference *arL = createFullAttrReference(attrIgNameL, 0,
										listPosString(LattrNames,attrIgNameL), 0,
										isPrefix(attrIgNameL,"ig") ? DT_BIT15 : n->attrType);

				CastExpr *castL;

				castL = createCastExpr((Node *) arL, DT_STRING);

				functioninput = appendToTailOfList(functioninput, castL);
				functioninput = appendToTailOfList(functioninput, createConstString("000000000000000"));
				FunctionCall *hammingdist = createFunctionCall("hammingdist", functioninput);

				exprs = appendToTailOfList(exprs,hammingdist);
				atNames = appendToTailOfList(atNames, CONCAT_STRINGS("hamming_", n->name));
				x++;
			}
		}
	}

	FOREACH(AttributeReference, n, RprojExprs)
	{
		List *functioninput = NIL;
		boolean flag = searchListString(joinNames, n->name);
		if(!isPrefix(n->name, "ig") && flag == FALSE)
		{
			char *ch = replaceSubstr(n->name, "1", "");
			if(MAP_HAS_STRING_KEY(nameToIgAttrNameL, ch) && !isSuffix(n->name, "anno") )
			{
				x++;
				continue;
			}
			else if(!MAP_HAS_STRING_KEY(nameToIgAttrNameL, ch) && !isSuffix(n->name, "anno"))
			{
				char *attrIgNameR = STRING_VALUE(MAP_GET_STRING(nameToIgAttrNameR, ch));

				AttributeReference *arR = createFullAttrReference(attrIgNameR, 0,
										LIST_LENGTH(LattrNames) + listPosString(RattrNames,attrIgNameR) - (lenL + 1),
										0, isPrefix(attrIgNameR,"ig") ? DT_BIT15 : n->attrType);

				CastExpr *castR;
				castR = createCastExpr((Node *) arR, DT_STRING);

				functioninput = appendToTailOfList(functioninput, castR);
				functioninput = appendToTailOfList(functioninput, createConstString("000000000000000"));
				FunctionCall *hammingdist = createFunctionCall("hammingdist", functioninput);

				exprs = appendToTailOfList(exprs,hammingdist);
				atNames = appendToTailOfList(atNames, CONCAT_STRINGS("hamming_", n->name));
				x++;
			}
		}
	}


	ProjectionOperator *hamming_op = createProjectionOp(exprs, NULL, NIL, atNames);

    addChildOperator((QueryOperator *) hamming_op, (QueryOperator *) op1);
    switchSubtrees((QueryOperator *) op1, (QueryOperator *) hamming_op);

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
//

    //Adding hammingdistvalue function
	List *h_valueExprs = NIL;
	List *h_valueName = NIL;
	int posV = 0;


	FOREACH(AttributeDef, a, hamming_op->op.schema->attrDefs)
	{
		if(isPrefix(a->attrName, "hamming"))
		{
			AttributeReference *ar = createFullAttrReference(a->attrName, 0, posV,0, a->dataType);
			FunctionCall *hammingdistvalue = createFunctionCall("hammingdistvalue", singleton(ar));
			h_valueExprs = appendToTailOfList(h_valueExprs, hammingdistvalue);
			h_valueName = appendToTailOfList(h_valueName, CONCAT_STRINGS("value_", a->attrName));
			posV++;
		}

		else
		{
			AttributeReference *ar = createFullAttrReference(a->attrName, 0, posV,0, a->dataType);
			h_valueExprs = appendToTailOfList(h_valueExprs, ar);
			h_valueName = appendToTailOfList(h_valueName, a->attrName);
			posV++;
		}
	}

	ProjectionOperator *hammingvalue_op = createProjectionOp(h_valueExprs, NULL, NIL, h_valueName);

	addChildOperator((QueryOperator *) hammingvalue_op, (QueryOperator *) hamming_op);
	switchSubtrees((QueryOperator *) hamming_op, (QueryOperator *) hammingvalue_op);


	return hammingvalue_op;

}

*/

