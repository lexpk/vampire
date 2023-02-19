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
 * @file InductionRewriting.hpp
 * Defines class InductionRewriting
 *
 */

#ifndef __InductionRewriting__
#define __InductionRewriting__

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

class SingleOccurrenceReplacementIterator : public IteratorCore<Literal*> {
public:
  CLASS_NAME(SingleOccurrenceReplacementIterator);
  USE_ALLOCATOR(SingleOccurrenceReplacementIterator);
  SingleOccurrenceReplacementIterator(Literal* lit, Term* o, TermList r)
      : _lit(lit), _o(o), _r(r), _occurrences(_lit->countSubtermOccurrences(TermList(_o))) {}

  bool hasNext() override {
    return _iteration < _occurrences;
  }
  Literal* next() override;

private:
  unsigned _iteration = 0;
  Literal* _lit;
  Term* _o;
  TermList _r;
  unsigned _occurrences;

  class Replacer : public TermTransformer {
  public:
    Replacer(Term* o, TermList r, unsigned i)
      : _o(o), _r(r), _i(i), _matchCount(0) {}

  private:
    TermList transformSubterm(TermList trm) override;

    Term* _o;
    TermList _r;
    unsigned _i;
    unsigned _matchCount;
  };
};

using LitArgPair = pair<Literal*,TermList>;
using LitArgPairIter = VirtualIterator<LitArgPair>;

class InductionRewriting
: public GeneratingInferenceEngine
{
public:
  CLASS_NAME(InductionRewriting);
  USE_ALLOCATOR(InductionRewriting);

  InductionRewriting(bool downward) : _downward(downward) {}

  void attach(SaturationAlgorithm* salg) override;
  void detach() override;
  ClauseIterator generateClauses(Clause* premise) override;
  void output();

  static LitArgPairIter getTermIterator(Clause* premise, const Options& opt, Ordering& ord, bool downward);
  static LitArgPairIter getLHSIterator(Clause* premise, const Options& opt, Ordering& ord, bool downward);
  static void markTheoryAxiomsForLemmaGeneration();

private:
  ClauseIterator perform(
    Clause* rwClause, Literal* rwLit, TermList rwArg, TermList rwTerm,
    Clause* eqClause, Literal* eqLit, TermList eqLHS,
    ResultSubstitutionSP subst, bool eqIsResult);

  bool filterByHeuristics(
    Clause* rwClause, Literal* rwLit, TermList rwTerm,
    Clause* eqClause, Literal* eqLit, TermList eqLHS,
    ResultSubstitutionSP subst);

  TermIndex* _lhsIndex;
  TermIndex* _termIndex;
  DHMap<Clause*, unsigned> _eqs;
  bool _downward;
};

}

#endif /*__InductionRewriting__*/
