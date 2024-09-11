// ig_functions.h



#ifndef IG_FUNCTIONS_H_
#define IG_FUNCTIONS_H_

#include "model/query_operator/query_operator.h"

extern List *getARfromAttrDefs(List *attrDefs);
extern List *getNamesfromAttrDefs(List *attrDefs);
extern List *getARfromAttrDefswPos(QueryOperator *qo, List *attrDefs);
extern char *getTableNamefromPo(ProjectionOperator *po);
extern List *getARfromPoAr(ProjectionOperator *po);
extern List *getNamesfromPoAr(ProjectionOperator *po);

extern int searchArList(List *arList, char *ch);
extern int searchAdefList(List *adefList, char *ch);

extern List *removeDupeAr(List *arList);
extern int searchArListByPos(List *arList, int pos);
AttributeReference *getAttrRefFromArListByPos(List* arList, int pos);
extern int searchArListForPos(List *arList, char *ch);

extern QueryOperator *rewriteIG_test (QueryOperator *qo);

//Input : AttributeReference (Data Type : DT_STRING)
//Pitput : array of Ascii codes of string (Data Type : DT_INT)
extern Ascii *convertArtoAscii(AttributeReference *ar);


//Input : ProjectionOperator
//Output : List of converted ar(toAscii) and rest of the attributes
extern List *toAsciiList(ProjectionOperator *po);

//Input : List of projection expressions(contains Ascii, AttributeReference, CastExpr)
extern List *getAsciiAggrs(List *projExprs);

//clean up functions
extern QueryOperator *cleanEXPL(QueryOperator *qo);

extern int hasAscii(List *arList);

extern int searchCasePosinArList(List *arList);



#endif /* IG_FUNCTIONS_H_ */
