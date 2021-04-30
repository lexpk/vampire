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
 * @file InductionSchemeGenerator.hpp
 * Defines classes for generating induction schemes from function terms
 */

#ifndef __InductionSchemeGenerator__
#define __InductionSchemeGenerator__

#include "Forwards.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermTransformer.hpp"
#include "Indexing/Index.hpp"
#include "InductionPreprocessor.hpp"
#include "Lib/STL.hpp"

#include <bitset>

namespace Shell {

using namespace Kernel;
using namespace Lib;
using namespace Indexing;

class Occurrences {
public:
  Occurrences(bool initial)
    : _occ(1 & initial), _iter(), _max(1 << 1), _finished(false) {}

  void add(bool val) {
    ASS(!_finished);
    _occ <<= 1;
    _max <<= 1;
    _occ |= (1 & val);
  }

  void finalize() {
    ASS(!_finished);
    _finished = true;
    const auto c = num_bits();
    auto temp = _occ;
    _occ = 0;
    for (uint64_t i = 0; i < c; i++) {
      _occ <<= 1;
      _occ |= temp & 1;
      temp >>= 1;
    }
    _iter = _occ;
  }

  bool next() {
    ASS(_finished);
    _iter++;
    _iter |= _occ;
    return _iter < _max;
  }

  bool pop_last() {
    ASS(_finished);
    bool res = _iter & 1;
    _iter >>= 1;
    _max >>= 1;
    return res;
  }

  uint64_t val() {
    ASS(_finished);
    return _iter;
  }

  uint64_t num_bits() const {
    ASS(_finished);
    return __builtin_ctz(_max);
  }

  uint64_t num_set_bits() const {
    return __builtin_popcount(_occ);
  }

  void set_bits() {
    _iter = _max - 1;
  }

  void reset_bits() {
    _iter = _occ;
  }

  vstring toString() const {
    vstringstream str;
    auto temp = _iter;
    for (uint64_t i = 0; i < num_bits(); i++) {
      str << (temp & 1);
      temp >>= 1;
    }
    return str.str();
  }

private:
  uint64_t _occ;
  uint64_t _iter;
  uint64_t _max;
  bool _finished;
};

using OccurrenceMap = vmap<pair<Literal*, TermList>, Occurrences>;

/**
 * Replaces a subset of occurrences for given TermLists
 */
class TermReplacement2 : public TermTransformer {
public:
  TermReplacement2(const vmap<TermList, TermList>& r) : _r(r) {}
  TermList transformSubterm(TermList trm) override;

private:
  const vmap<TermList, TermList>& _r;
};

/**
 * Replaces a subset of occurrences for given TermLists
 */
class TermOccurrenceReplacement2 : public TermTransformer {
public:
  TermOccurrenceReplacement2(const vmap<TermList, TermList>& r,
                             const OccurrenceMap& occ, Literal* lit)
                            : _r(r), _o(occ), _lit(lit) {}
  TermList transformSubterm(TermList trm) override;

private:
  const vmap<TermList, TermList>& _r;
  OccurrenceMap _o;
  Literal* _lit;
};

/**
 * An instantiated induction template for a term.
 */
class InductionScheme
{
public:
  struct Case {
    Case() = default;
    Case(vvector<vmap<TermList, TermList>>&& recursiveCalls,
                    vmap<TermList, TermList>&& step)
      : _recursiveCalls(recursiveCalls), _step(step) {}
    bool contains(const Case& other, unsigned& var) const;

    vvector<vmap<TermList, TermList>> _recursiveCalls;
    vmap<TermList, TermList> _step;
  };

  void addCase(vvector<vmap<TermList, TermList>>&& recursiveCalls, vmap<TermList, TermList>&& step) {
    _cases.emplace_back(std::move(recursiveCalls), std::move(step));
  }
  void addCase(Case&& c) {
    _cases.push_back(std::move(c));
  }
  bool finalize();
  static TermList createRepresentingTerm(const vset<TermList>& inductionTerms, const vmap<TermList,TermList>& r, unsigned& var);
  const vvector<Case>& cases() const { ASS(_finalized); return _cases; }
  const vset<TermList>& inductionTerms() const { ASS(_finalized); return _inductionTerms; }
  unsigned maxVar() const { ASS(_finalized); return _maxVar; }

private:
  void addBaseCases();

  vvector<Case> _cases;
  unsigned _maxVar;
  vset<TermList> _inductionTerms;
  bool _finalized = false;
};

ostream& operator<<(ostream& out, const InductionScheme& scheme);

/**
 * This class instantiates the induction templates from a literal
 * we want to induct on. Afterwards, stores these and filters them.
 * Also stores all active occurrences of possible induction terms.
 */
struct InductionSchemeGenerator {
  virtual void generate(
    const SLQueryResult& main,
    const vset<pair<Literal*,Clause*>>& side,
    vvector<pair<InductionScheme, OccurrenceMap>>& res) = 0;
};

struct RecursionInductionSchemeGenerator
  : public InductionSchemeGenerator
{
  void generate(const SLQueryResult& main,
    const vset<pair<Literal*,Clause*>>& side,
    vvector<pair<InductionScheme, OccurrenceMap>>& res) override;

private:
  void generate(Clause* premise, Literal* lit,
    vvector<InductionScheme>& schemes);
  void process(TermList curr, bool active,
    Stack<bool>& actStack, Clause* premise, Literal* lit,
    vvector<InductionScheme>& schemes);
  void addScheme(Literal* lit, Term* t, const InductionTemplate& templ,
    vvector<InductionScheme>& schemes);

  OccurrenceMap _actOccMaps;
  bool _aggressiveMode = false;
};

struct StructuralInductionSchemeGenerator
  : public InductionSchemeGenerator
{
  void generate(const SLQueryResult& main,
    const vset<pair<Literal*,Clause*>>& side,
    vvector<pair<InductionScheme, OccurrenceMap>>& res) override;

private:
  InductionScheme generateStructural(Term* term);
};

} // Shell

#endif