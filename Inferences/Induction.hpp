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
 * @file Induction.hpp
 * Defines class Induction
 *
 */

#ifndef __Induction__
#define __Induction__

#include <cmath>

#include "Forwards.hpp"

#include "Indexing/InductionFormulaIndex.hpp"
#include "Indexing/LiteralIndex.hpp"
#include "Indexing/TermIndex.hpp"

#include "Kernel/TermTransformer.hpp"
#include "Kernel/Theory.hpp"

#include "Lib/DHMap.hpp"
#include "Lib/DHSet.hpp"
#include "Lib/List.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/FunctionDefinitionHandler.hpp"

#include "InductionHelper.hpp"
#include "InferenceEngine.hpp"

namespace Inferences
{

using namespace Kernel;
using namespace Saturation;
using namespace Shell;
using namespace Lib;

class ActiveOccurrenceIterator
  : public IteratorCore<TermList>
{
public:
  ActiveOccurrenceIterator(Term* term, FunctionDefinitionHandler* fnDefHandler)
  : _stack(8), _fnDefHandler(fnDefHandler)
  {
    _stack.push(term);
    ASS(term->ground());
    ActiveOccurrenceIterator::next();
  }

  bool hasNext() override { return !_stack.isEmpty(); }
  TermList next() override;
private:
  Stack<Term*> _stack;
  FunctionDefinitionHandler* _fnDefHandler;
};

Term* getPlaceholderForTerm(const vvector<Term*>& ts, unsigned i);

class TermReplacement : public TermTransformer {
public:
  TermReplacement(const vmap<Term*, TermList>& m) : _m(m) {}
  TermList transformSubterm(TermList trm) override;
protected:
  vmap<Term*,TermList> _m;
};

class SkolemSquashingTermReplacement : public TermReplacement {
public:
  SkolemSquashingTermReplacement(const vmap<Term*, TermList>& m, unsigned& var)
    : TermReplacement(m), _v(var) {}
  TermList transformSubterm(TermList trm) override;
  DHMap<Term*, unsigned> _tv; // maps terms to their variable replacement
private:
  unsigned& _v;               // fresh variable counter supported by caller
};

struct InductionContext {
  explicit InductionContext(vvector<Term*>&& ts)
    : _indTerms(ts) {}
  explicit InductionContext(const vvector<Term*>& ts)
    : _indTerms(ts) {}
  InductionContext(const vvector<Term*>& ts, Literal* l, Clause* cl)
    : InductionContext(ts)
  {
    insert(cl, l);
  }

  void insert(Clause* cl, Literal* lit) {
    // this constructs an empty inner map if cl is not yet mapped
    auto node = _cls.emplace(cl, LiteralStack()).first;
    node->second.push(lit);
  }

  Formula* getFormula(const vvector<TermList>& r, bool opposite, Substitution* subst = nullptr) const;
  Formula* getFormulaWithSquashedSkolems(const vvector<TermList>& r, bool opposite, unsigned& var,
    VList** varList = nullptr, Substitution* subst = nullptr) const;

  vstring toString() const {
    vstringstream str;
    for (const auto& indt : _indTerms) {
      str << *indt << endl;
    }
    for (const auto& kv : _cls) {
      str << *kv.first << endl;
      for (const auto& lit : kv.second) {
        str << *lit << endl;
      }
    }
    return str.str();
  }

  vvector<Term*> _indTerms;
  // One could induct on all literals of a clause, but if a literal
  // doesn't contain the induction term, it just introduces a couple
  // of tautologies and duplicate literals (a hypothesis clause will
  // be of the form ~L v L v C, other clauses L v L v C). So instead,
  // we only store the literals we actually induct on. An alternative
  // would be storing indices but then we need to pass around the
  // clause as well.
  vunordered_map<Clause*, LiteralStack> _cls;
private:
  Formula* getFormula(TermReplacement& tr, bool opposite) const;
};

class ContextReplacement
  : public TermReplacement, public IteratorCore<InductionContext> {
public:
  ContextReplacement(const InductionContext& context);

  bool hasNext() override {
    return !_used;
  }
  InductionContext next() override;

protected:
  InductionContext _context;
  bool _used;
};

class ActiveOccurrenceContextReplacement
  : public ContextReplacement {
public:
  ActiveOccurrenceContextReplacement(const InductionContext& context, FunctionDefinitionHandler* fnDefHandler);
  InductionContext next() override;
  bool hasNonActive() const { return _hasNonActive; }

protected:
  TermList transformSubterm(TermList trm) override;

private:
  FunctionDefinitionHandler* _fnDefHandler;
  vvector<unsigned> _iteration;
  vvector<unsigned> _matchCount;
  bool _hasNonActive;
};

class ContextSubsetReplacement
  : public ContextReplacement {
public:
  ContextSubsetReplacement(const InductionContext& context, const unsigned maxSubsetSize);

  bool hasNext() override;
  InductionContext next() override;

protected:
  TermList transformSubterm(TermList trm) override;

private:
  bool shouldSkipIteration() const;
  void stepIteration();
  // _iteration serves as a map of occurrences to replace
  vvector<unsigned> _iteration;
  vvector<unsigned> _maxIterations;
  // Counts how many occurrences were already encountered in one transformation
  vvector<unsigned> _matchCount;
  const unsigned _maxOccurrences = 1 << 20;
  const unsigned _maxSubsetSize;
  bool _ready;
  bool _done;
};

class Induction
: public GeneratingInferenceEngine
{
public:
  CLASS_NAME(Induction);
  USE_ALLOCATOR(Induction);

  void attach(SaturationAlgorithm* salg) override;
  void detach() override;

  ClauseIterator generateClauses(Clause* premise) override;

#if VDEBUG
  void setTestIndices(const Stack<Index*>& indices) override {
    _comparisonIndex = static_cast<LiteralIndex*>(indices[0]);
    _inductionTermIndex = static_cast<TermIndex*>(indices[1]);
    _structInductionTermIndex = static_cast<TermIndex*>(indices[2]);
  }
#endif // VDEBUG

private:
  // The following pointers can be null if int induction is off.
  LiteralIndex* _comparisonIndex = nullptr;
  TermIndex* _inductionTermIndex = nullptr;
  TermIndex* _structInductionTermIndex = nullptr;
  InductionFormulaIndex _formulaIndex;
  InductionFormulaIndex _recFormulaIndex;
};

class InductionClauseIterator
{
public:
  // all the work happens in the constructor!
  InductionClauseIterator(Clause* premise, InductionHelper helper, SaturationAlgorithm* salg,
    TermIndex* structInductionTermIndex, InductionFormulaIndex& formulaIndex)
      : _helper(helper), _opt(salg->getOptions()), _structInductionTermIndex(structInductionTermIndex),
      _formulaIndex(formulaIndex), _fnDefHandler(salg->getFunctionDefinitionHandler())
  {
    processClause(premise);
  }

  CLASS_NAME(InductionClauseIterator);
  USE_ALLOCATOR(InductionClauseIterator);
  DECL_ELEMENT_TYPE(Clause*);

  inline bool hasNext() { return _clauses.isNonEmpty(); }
  inline OWN_ELEMENT_TYPE next() { 
    return _clauses.pop();
  }

private:
  void processClause(Clause* premise);
  void processLiteral(Clause* premise, Literal* lit);
  void processIntegerComparison(Clause* premise, Literal* lit);

  ClauseStack produceClauses(Formula* hypothesis, InferenceRule rule, const InductionContext& context);
  void resolveClauses(InductionContext context, InductionFormulaIndex::Entry* e, const TermQueryResult* bound1, const TermQueryResult* bound2);
  void resolveClauses(const ClauseStack& cls, const InductionContext& context, Substitution& subst, bool applySubst = false);

  void performFinIntInduction(const InductionContext& context, const TermQueryResult& lb, const TermQueryResult& ub);
  void performInfIntInduction(const InductionContext& context, bool increasing, const TermQueryResult& bound);
  void performIntInduction(const InductionContext& context, InductionFormulaIndex::Entry* e, bool increasing, const TermQueryResult& bound1, const TermQueryResult* optionalBound2);

  void performStructInductionOne(const InductionContext& context, InductionFormulaIndex::Entry* e);
  void performStructInductionTwo(const InductionContext& context, InductionFormulaIndex::Entry* e);
  void performStructInductionThree(const InductionContext& context, InductionFormulaIndex::Entry* e);
  void performRecursionInduction(const InductionContext& context, const InductionTemplate* templ, InductionFormulaIndex::Entry* e);

  bool notDoneInt(InductionContext context, Literal* bound1, Literal* bound2, InductionFormulaIndex::Entry*& e);

  Stack<Clause*> _clauses;
  InductionHelper _helper;
  const Options& _opt;
  TermIndex* _structInductionTermIndex;
  InductionFormulaIndex& _formulaIndex;
  FunctionDefinitionHandler* _fnDefHandler;
};

};

#endif /*__Induction__*/
