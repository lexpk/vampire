/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "InductionSchemeGenerator.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/TermIterators.hpp"

#include "Inferences/InductionHelper.hpp"

using namespace Kernel;

namespace Shell {

inline bool isTermAlgebraCons(Term* t)
{
  ASS(!t->isLiteral());
  return env.signature->getFunction(t->functor())->termAlgebraCons();
}

/**
 * Returns all subterms which can be inducted on for a term.
 */
vset<Term*> getInductionTerms(Term* t, TermList s)
{
  CALL("getInductionTerms");
  // no predicates here
  ASS(!t->isLiteral());

  vset<Term*> res;
  Stack<Term*> todo;
  todo.push(t);

  while (todo.isNonEmpty()) {
    auto curr = todo.pop();

    if (res.count(curr)) {
      continue;
    }

    unsigned f = curr->functor();
    auto type = env.signature->getFunction(f)->fnType();
    if (canInductOn(curr) && type->result() == s) {
      res.insert(curr);
    }

    // If function with recursive definition,
    // recurse in its active arguments
    if (env.signature->getFnDefHandler()->hasInductionTemplate(f, true /*trueFun*/)) {
      auto templ = env.signature->getFnDefHandler()->getInductionTemplate(f, true /*trueFun*/);
      const auto& indVars = templ->inductionPositions();

      Term::Iterator argIt(curr);
      unsigned i = 0;
      while (argIt.hasNext()) {
        auto arg = argIt.next();
        if (indVars.at(i) && arg.isTerm()) {
          todo.push(arg.term());
        }
        i++;
      }
    } else if (isTermAlgebraCons(curr)) {
      for (unsigned i = 0; i < curr->arity(); i++) {
        if (type->arg(i) == type->result()) {
          auto st = *curr->nthArgument(i);
          if (st.isTerm()) {
            todo.push(st.term());
          }
        }
      }
    } else {
      for (unsigned i = 0; i < curr->arity(); i++) {
        auto st = *curr->nthArgument(i);
        if (st.isTerm()) {
          todo.push(st.term());
        }
      }
    }
  }
  return res;
}

void RecursionInductionSchemeGenerator::generate(
  const SLQueryResult& main,
  const vset<pair<Literal*,Clause*>>& side,
  vvector<pair<InductionScheme, OccurrenceMap>>& res)
{
  CALL("RecursionInductionSchemeGenerator::generate/1");

  _schemes.clear();
  _actOccMaps._m.clear();

  static vset<Literal*> litsProcessed;
  litsProcessed.clear();
  litsProcessed.insert(main.literal);

  generate(main.clause, main.literal);
  for (const auto& s : side) {
    if (litsProcessed.insert(s.first).second) {
      generate(s.second, s.first);
    }
  }
  _actOccMaps.finalize();
  // filter out schemes that only contain induction
  // terms not present in the main literal
  for (auto it = _schemes.begin(); it != _schemes.end();) {
    static const bool filterC = env.options->inductionOnComplexTermsHeuristic();
    bool filter = true;
    for (const auto& kv : it->inductionTerms()) {
      auto c = !skolem(kv.first);
      unsigned occ = 0;
      for (const auto& kv2 : _actOccMaps._m) {
        if (kv.first == kv2.first.second) {
          if (c) {
            occ += kv2.second.num_bits();
          }
          if (kv2.first.first == main.literal && kv2.second.num_set_bits()) {
            filter = false;
          }
        }
      }
      if (filterC && occ == 1) {
        filter = true;
        break;
      }
    }
    if (filter) {
      it = _schemes.erase(it);
    } else {
      it++;
    }
  }

  for (const auto& sch : _schemes) {
    res.push_back(make_pair(sch, _actOccMaps.create_necessary(sch)));
  }
}

void RecursionInductionSchemeGenerator::generate(Clause* premise, Literal* lit)
{
  CALL("RecursionInductionSchemeGenerator::generate/2");

  // Process all subterms of the literal to
  // be able to store occurrences of induction
  // terms. The literal itself and both sides
  // of the equality count as active positions.

  if (env.options->showInduction()) {
    env.beginOutput();
    env.out() << "[Induction] processing literal " << *lit << endl;
    env.endOutput();
  }

  _actStack.reset();
  process(lit);
  SubtermIterator it(lit);
  while (it.hasNext()){
    TermList curr = it.next();
    bool active = _actStack.pop();
    if (curr.isTerm()) {
      process(curr.term(), active, lit);
    }
  }
  ASS(_actStack.isEmpty());
}

void RecursionInductionSchemeGenerator::handleActiveTerm(Term* t, InductionTemplate* templ)
{
  CALL("RecursionInductionSchemeGenerator::handleActiveTerm");

  const auto& indPos = templ->inductionPositions();

  for (int i = t->arity()-1; i >= 0; i--) {
    _actStack.push(indPos[i]);
  }

  static bool exhaustive = env.options->inductionExhaustiveGeneration();
  if (exhaustive) {
    Term::Iterator argIt(t);
    auto f = t->functor();
    auto type = t->isLiteral() ? env.signature->getPredicate(f)->predType() : env.signature->getFunction(f)->fnType();
    unsigned i = 0;
    vvector<TermStack> argTermsList(1); // initially 1 empty vector
    while (argIt.hasNext()) {
      auto arg = argIt.next();
      if (!indPos[i] || arg.isVar()) {
        for (auto& argTerms : argTermsList) {
          argTerms.push(arg);
        }
      } else {
        auto its = getInductionTerms(arg.term(), type->arg(i));
        vvector<TermStack> newArgTermsList;
        for (const auto& indTerm : its) {
          for (auto argTerms : argTermsList) {
            argTerms.push(TermList(indTerm));
            newArgTermsList.push_back(std::move(argTerms));
          }
        }
        argTermsList = newArgTermsList;
      }
      i++;
    }

    auto isLit = t->isLiteral();
    for (const auto& argTerms : argTermsList) {
      Term* nt;
      if (isLit) {
        nt = Literal::create(static_cast<Literal*>(t), argTerms.begin());
      } else {
        nt = Term::create(t, argTerms.begin());
      }
      templ->requestInductionScheme(nt, _schemes);
    }
  } else {
    templ->requestInductionScheme(t, _schemes);
  }
}

void RecursionInductionSchemeGenerator::process(Term* t, bool active, Literal* lit)
{
  CALL("RecursionInductionSchemeGenerator::process");

  // If induction term, store the occurrence
  if (canInductOn(t)) {
    _actOccMaps.add(lit, t, active);
  }

  unsigned f = t->functor();

  // If function with recursive definition, create a scheme
  if (active && env.signature->getFnDefHandler()->hasInductionTemplate(f, true)) {
    handleActiveTerm(t, env.signature->getFnDefHandler()->getInductionTemplate(f, true));
  } else {
    for (unsigned i = 0; i < t->arity(); i++) {
      _actStack.push(active);
    }
  }
}

void RecursionInductionSchemeGenerator::process(Literal* lit)
{
  CALL("RecursionInductionSchemeGenerator::process");

  unsigned f = lit->functor();

  // If function with recursive definition, create a scheme
  if (env.signature->getFnDefHandler()->hasInductionTemplate(f, false)) {
    handleActiveTerm(lit, env.signature->getFnDefHandler()->getInductionTemplate(f, false));
  } else {
    for (unsigned i = 0; i < lit->arity(); i++) {
      _actStack.push(true);
    }
  }
}

void StructuralInductionSchemeGenerator::generate(
  const SLQueryResult& main,
  const vset<pair<Literal*,Clause*>>& side,
  vvector<pair<InductionScheme, OccurrenceMap>>& res)
{
  CALL("StructuralInductionSchemeGenerator::generate");

  vvector<InductionScheme> schemes;
  OccurrenceMap occMap;

  Set<Term*> ta_terms;
  SubtermIterator it(main.literal);
  while (it.hasNext()) {
    TermList ts = it.next();
    ASS(ts.isTerm());
    Term* t = ts.term();
    unsigned f = t->functor();
    if (Inferences::InductionHelper::isInductionTermFunctor(f) &&
        Inferences::InductionHelper::isStructInductionFunctor(f)) {
      ta_terms.insert(t);
    }
    occMap.add(main.literal, t, false);
  }

  Set<Term*>::Iterator taIt(ta_terms);
  while (taIt.hasNext()) {
    env.signature->getFnDefHandler()->requestStructuralInductionScheme(taIt.next(), schemes);
  }

  for (const auto& qr : side) {
    SubtermIterator it(qr.first);
    while (it.hasNext()) {
      Term* t = it.next().term();
      occMap.add(qr.first, t, false);
    }
  }

  occMap.finalize();
  for (const auto& sch : schemes) {
    res.push_back(make_pair(sch, occMap.create_necessary(sch)));
  }
}

} // Shell
