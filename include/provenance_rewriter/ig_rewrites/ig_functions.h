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


extern QueryOperator *rewriteIG_test (QueryOperator *op);

//Input : AttributeReference (Data Type : DT_STRING)
//Pitput : array of Ascii codes of string (Data Type : DT_INT)
extern Ascii *convertArtoAscii(AttributeReference *);


//Input : ProjectionOperator
//Output : List of converted ar(toAscii) and rest of the attributes
extern List *toAsciiList(ProjectionOperator *);

//Input : List of projection expressions(contains Ascii, AttributeReference, CastExpr)
extern List *getAsciiAggrs(List *, ProjectionOperator *);


#endif /* IG_FUNCTIONS_H_ */
