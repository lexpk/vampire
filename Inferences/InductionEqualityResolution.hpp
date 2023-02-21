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
 * @file InductionEqualityResolution.hpp
 * Defines class InductionEqualityResolution.
 */

#ifndef __InductionEqualityResolution__
#define __InductionEqualityResolution__

#include "Forwards.hpp"

#include "InferenceEngine.hpp"

namespace Inferences {

using namespace Kernel;

class InductionEqualityResolution
: public GeneratingInferenceEngine
{
public:
  CLASS_NAME(InductionEqualityResolution);
  USE_ALLOCATOR(InductionEqualityResolution);

  ClauseIterator generateClauses(Clause* premise);
};

};

#endif /* __InductionEqualityResolution__ */
