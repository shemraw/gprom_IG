// ig_functions.h



#ifndef IG_FUNCTIONS_H_
#define IG_FUNCTIONS_H_

#include "model/query_operator/query_operator.h"

static ProjectionOperator *rewriteIG_SumExprs(ProjectionOperator *op);
static ProjectionOperator *rewriteIG_HammingFunctions(ProjectionOperator *op);

#endif /* IG_FUNCTIONS_H_ */
