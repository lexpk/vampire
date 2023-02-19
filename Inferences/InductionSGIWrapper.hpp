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
 * @file InductionSGIWrapper.hpp
 * Defines class InductionSGIWrapper
 *
 */

#ifndef __InductionSGIWrapper__
#define __InductionSGIWrapper__

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

class InductionResolution;
class InductionRewriting;

class InductionSGIWrapper
: public SimplifyingGeneratingInference
{
public:
  CLASS_NAME(InductionSGIWrapper);
  USE_ALLOCATOR(InductionSGIWrapper);

  InductionSGIWrapper(GeneratingInferenceEngine* induction,
      InductionResolution* resolution,
      InductionRewriting* dwRewriting,
      InductionRewriting* uwRewriting,
      SimplifyingGeneratingInference* generator)
    : _induction(induction), _resolution(resolution),
      _dwRewriting(dwRewriting), _uwRewriting(uwRewriting), _generator(generator) {}

  ClauseGenerationResult generateSimplify(Clause* premise) override;

  void attach(SaturationAlgorithm* salg) override
  {
    _generator->attach(salg);
  }
  void detach() override
  {
    _generator->detach();
  }
private:
  GeneratingInferenceEngine* _induction;
  InductionResolution* _resolution;
  InductionRewriting* _dwRewriting;
  InductionRewriting* _uwRewriting;
  ScopedPtr<SimplifyingGeneratingInference> _generator;
};

}

#endif /*__InductionSGIWrapper__*/
