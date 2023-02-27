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
 * @file InductionSGIWrapper.cpp
 * Implements class InductionSGIWrapper.
 */

#include "Lib/Metaiterators.hpp"

#include "Kernel/RobSubstitution.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/TermIterators.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "InductionSGIWrapper.hpp"
#include "InductionResolution.hpp"
#include "InductionRewriting.hpp"

namespace Inferences {

SimplifyingGeneratingInference::ClauseGenerationResult InductionSGIWrapper::generateSimplify(Clause* premise)
{
  CALL("InductionSGIWrapper::generateSimplify");
  // static unsigned cnt = 0;
  // cnt++;
  // if (cnt % 1000 == 0) {
  //   _dwRewriting->output();
  //   _uwRewriting->output();
  // }
  // if (!premise->getRewritingLowerBound() && !premise->getRewritingUpperBound()) {
  if (!premise->isFromUpwardParamodulation()) {
    return _generator->generateSimplify(premise);
  }
  // ASS(!premise->getRewritingLowerBound() || !premise->getRewritingUpperBound());
  auto it = ClauseIterator::getEmpty();
  // if (premise->getRewritingUpperBound()) {
  //   it = pvi(getConcatenatedIterator(it, _dwRewriting->generateClauses(premise)));
  //   // it = pvi(getConcatenatedIterator(it, _resolution->generateClauses(premise)));
  // }
  return ClauseGenerationResult {
    .clauses = pvi(iterTraits(it).concat(
      _induction->generateClauses(premise),
      _uwRewriting->generateClauses(premise))),
    .premiseRedundant = false,
  };
}

}
