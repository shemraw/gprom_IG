// ig_functions.h



#ifndef IG_FUNCTIONS_H_
#define IG_FUNCTIONS_H_

#include "model/query_operator/query_operator.h"

//typedef struct AsciiAggrs {
//    List *aggrNames;
//    List *groupBy;
//    List *aggrs;
//} AsciiAggrs;
//


extern List *getARfromAttrDefs(List *attrDefs);
extern List *getNamesfromAttrDefs(List *attrDefs);
extern List *getARfromAttrDefswPos(QueryOperator *qo, List *attrDefs);
extern char *getTableNamefromPo(ProjectionOperator *po);
extern List *getARfromPoAr(ProjectionOperator *po);
extern List *getNamesfromPoAr(ProjectionOperator *po);



extern QueryOperator *rewriteIG_test (QueryOperator *qo);

//Input : AttributeReference (Data Type : DT_STRING)
//Pitput : array of Ascii codes of string (Data Type : DT_INT)
extern Ascii *convertArtoAscii(AttributeReference *ar);


//Input : ProjectionOperator
//Output : List of converted ar(toAscii) and rest of the attributes
extern List *toAsciiList(ProjectionOperator *po);

//Input : List of projection expressions(contains Ascii, AttributeReference, CastExpr)
extern List *getAsciiAggrs(List *projExprs, ProjectionOperator *po);


#endif /* IG_FUNCTIONS_H_ */
