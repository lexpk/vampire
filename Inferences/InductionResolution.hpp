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
 * @file InductionResolution.hpp
 * Defines class InductionResolution
 *
 */

#ifndef __InductionResolution__
#define __InductionResolution__

#include "Forwards.hpp"

#include "InferenceEngine.hpp"
#include "InductionHelper.hpp"

#include "Kernel/EqHelper.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/TermTransformer.hpp"

#include "Lib/ScopedPtr.hpp"
#include "Lib/SharedSet.hpp"

namespace Inferences
{

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class InductionResolution
: public GeneratingInferenceEngine
{
public:
  CLASS_NAME(InductionResolution);
  USE_ALLOCATOR(InductionResolution);

  void attach(SaturationAlgorithm* salg) override;
  void detach() override;
  ClauseIterator generateClauses(Clause* premise) override;

  static VirtualIterator<Literal*> getIterator(Ordering& ord, Clause* premise);

private:
  Clause* perform(Clause* queryCl, Literal* queryLit, SLQueryResult res);

  LiteralIndex* _index;
};

}

#endif /*__InductionResolution__*/
