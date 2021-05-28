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
 * @file Superposition.hpp
 * Defines class Superposition
 *
 */

#ifndef __IRC_Superposition__
#define __IRC_Superposition__

#include "Forwards.hpp"

#include "Inferences/InferenceEngine.hpp"
#include "Kernel/Ordering.hpp"
#include "Shell/UnificationWithAbstractionConfig.hpp"
#include "Indexing/InequalityResolutionIndex.hpp"
#include "Shell/Options.hpp"

namespace Inferences {
namespace IRC {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class Superposition
: public GeneratingInferenceEngine
{
public:
  CLASS_NAME(Superposition);
  USE_ALLOCATOR(Superposition);

  Superposition(Superposition&&) = default;
  Superposition(shared_ptr<IrcState> shared) 
    : _shared(std::move(shared))
    , _index(nullptr)
  {  }

  void attach(SaturationAlgorithm* salg) final override;
  void detach() final override;


  ClauseIterator generateClauses(Clause* premise) final override;

#if VDEBUG
  virtual void setTestIndices(Stack<Indexing::Index*> const&) final override;
#endif

private:

                            Option<ClauseIterator> generateClauses(Clause* clause, Literal* literal, IrcLiteral<IntTraits> lit) const;
  template<class NumTraits> Option<ClauseIterator> generateClauses(Clause* clause, Literal* literal, IrcLiteral<NumTraits> lit) const;

  shared_ptr<IrcState> _shared;
  IRCSuperpositionIndex* _index;
};

} // namespace IRC
} // namespace Inferences

// lalalalala
#endif /*__IRC_Superposition__*/