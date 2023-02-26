/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file InductionEqualityResolution.cpp
 * Implements class InductionEqualityResolution.
 */

#include "Lib/VirtualIterator.hpp"
#include "Lib/Metaiterators.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Saturation/SaturationAlgorithm.hpp"

#include "InductionEqualityResolution.hpp"

namespace Inferences
{

using namespace Lib;
using namespace Kernel;

ClauseIterator InductionEqualityResolution::generateClauses(Clause* premise)
{
  CALL("InductionEqualityResolution::generateClauses");

  return pvi(iterTraits(premise->iterLits())
    .filter([](Literal* lit) {
      return lit->isEquality() && lit->isNegative();
    })
    .map([premise](Literal* lit) -> Clause* {
      RobSubstitution subst;
      if (!subst.unify(lit->termArg(0),0,lit->termArg(1),0)) {
        return nullptr;   
      }

      auto len = premise->length();
      Clause* res = new(len-1) Clause(len-1, GeneratingInference1(InferenceRule::INDUCTION_EQUALITY_RESOLUTION, premise));

      unsigned next = 0;
      for (unsigned i=0; i < len; i++) {
        Literal* curr=(*premise)[i];
        if (curr != lit) {
          (*res)[next++] = subst.apply(curr, 0);
        }
      }
      ASS_EQ(next,len-1);

      env.statistics->inductionEqResolution++;
      auto lowerBound = premise->getRewritingLowerBound();
      if (lowerBound) {
        Term* lowerBoundS;
        if (lowerBound->isLiteral()) {
          lowerBoundS = subst.apply(static_cast<Literal*>(lowerBound), 0);
        } else {
          lowerBoundS = subst.apply(TermList(lowerBound), 0).term();
        }
        res->setRewritingBound(lowerBoundS, true);
      }
      auto upperBound = premise->getRewritingUpperBound();
      if (upperBound) {
        Term* upperBoundS;
        if (upperBound->isLiteral()) {
          upperBoundS = subst.apply(static_cast<Literal*>(upperBound), 0);
        } else {
          upperBoundS = subst.apply(TermList(upperBound), 0).term();
        }
        res->setRewritingBound(upperBoundS, false);
      }

      return res;
    })
    .filter(NonzeroFn()));
}

}
