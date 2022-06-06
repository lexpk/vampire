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
 * @file InductionPreprocessor.hpp
 * Defines helper classes for induction templates and preprocessing
 */

#ifndef __InductionPreprocessor__
#define __InductionPreprocessor__

#include "Forwards.hpp"
#include "Indexing/TermSubstitutionTree.hpp"
#include "Kernel/TermTransformer.hpp"
#include "TermAlgebra.hpp"
#include "Lib/STL.hpp"

namespace Shell {

using namespace Indexing;
using namespace Kernel;
using namespace Lib;

bool skolem(Term* t);
bool containsSkolem(Term* t);
bool canInductOn(Term* t);

using InductionTerms = vmap<Term*, unsigned>;

/**
 * An instantiated induction template for a term.
 */
class InductionScheme
{
public:
  InductionScheme(const InductionTerms& indTerms, bool noChecks = false)
    : _inductionTerms(indTerms), _finalized(false), _noChecks(noChecks), _cases() {}

  struct Case {
    Case() = default;
    Case(vvector<Substitution>&& recursiveCalls, Substitution&& step)
      : _recursiveCalls(recursiveCalls), _step(step) {}

    vvector<Substitution> _recursiveCalls;
    Substitution _step;
  };

  bool finalize();
  static Term* createRepresentingTerm(const InductionTerms& inductionTerms, const Substitution& s);
  const vvector<Case>& cases() const { ASS(_finalized); return *_cases; }
  const InductionTerms& inductionTerms() const { ASS(_finalized); return _inductionTerms; }
  bool operator<(const InductionScheme& other) const {
    return _inductionTerms < other._inductionTerms ||
      (_inductionTerms == other._inductionTerms && _cases < other._cases);
  }

private:
  bool addBaseCases();

  friend struct InductionTemplate;
  friend class FnDefHandler;

  InductionTerms _inductionTerms;
  bool _finalized;
  bool _noChecks;
  vvector<Case>* _cases;
};

ostream& operator<<(ostream& out, const InductionScheme& scheme);

/**
 * Corresponds to the branches of a function definition.
 * Stores the branches and the active positions
 * (i.e. the changing arguments) of the function.
 */
struct InductionTemplate {
  CLASS_NAME(InductionTemplate);
  USE_ALLOCATOR(InductionTemplate);
  InductionTemplate(const Term* t);

  void addBranch(vvector<Term*>&& recursiveCalls, Term*&& header);
  bool finalize();
  void requestInductionScheme(Term* t, vset<InductionScheme>& schemes);
  const vvector<bool>& inductionPositions() const { return _indPos; }
  bool matchesTerm(Term* t, vvector<Term*>& inductionTerms) const;

  /**
   * Stores the template for a recursive case
   * This includes:
   * - the step case
   * - the recursive calls
   *   (if not present it is a base case)
   */
  struct Branch {
    Branch(vvector<Term*>&& recursiveCalls, Term*&& header)
      : _recursiveCalls(recursiveCalls), _header(header) {}

    bool contains(const Branch& other) const;

    vvector<Term*> _recursiveCalls;
    Term* _header;
  };

  const vvector<Branch>& branches() const { return _branches; }

  const unsigned _functor;
  const unsigned _arity;
  const bool _isLit;
  const OperatorType* _type;

private:
  friend ostream& operator<<(ostream& out, const InductionTemplate& templ);

  bool checkUsefulness() const;
  bool checkWellFoundedness();
  void checkWellDefinedness();

  vvector<Branch> _branches;
  vvector<bool> _indPos;
  vvector<bool> _usedNonIndPos;

  vmap<vvector<TermList>, vvector<InductionScheme::Case>> _caseMap;
  vset<vvector<TermList>> _invalids;
};

ostream& operator<<(ostream& out, const InductionTemplate::Branch& branch);
ostream& operator<<(ostream& out, const InductionTemplate& templ);

class FnDefHandler
{
public:
  CLASS_NAME(FnDefHandler);
  USE_ALLOCATOR(FnDefHandler);

  FnDefHandler()
    : _is(new TermSubstitutionTree()) {}

  void handleClause(Clause* c, unsigned i, bool reversed);
  void finalize();
  void requestStructuralInductionScheme(Term* t, vvector<InductionScheme>& schemes);

  TermQueryResultIterator getGeneralizations(TermList t) {
    return _is->getGeneralizations(t, true);
  }

  bool hasInductionTemplate(unsigned fn, bool trueFun) const {
    return _templates.count(make_pair(fn, trueFun));
  }

  InductionTemplate* getInductionTemplate(unsigned fn, bool trueFun) {
    return _templates.at(make_pair(fn, trueFun));
  }

private:
  unique_ptr<TermIndexingStructure> _is;
  vmap<pair<unsigned, bool>, InductionTemplate*> _templates;
  vmap<TermAlgebra*, vvector<InductionScheme::Case>> _taCaseMap;
};

/**
 * This class generates the induction templates based on
 * the marked recursive function definitions from the parser.
 */
struct InductionPreprocessor {
  static void processCase(const unsigned fn, TermList body, vvector<Term*>& recursiveCalls);
  static bool checkWellFoundedness(const vvector<pair<Term*,Term*>>& relatedTerms);
  static bool checkWellDefinedness(const vvector<Term*>& cases, vvector<vvector<TermList>>& missingCases);
};

} // Shell

#endif
