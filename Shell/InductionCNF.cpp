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
 * @file InductionCNF.cpp
 * Implements class InductionCNF clausifying induction formulas.
 */

#include "Kernel/OperatorType.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Substitution.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/FormulaVarIterator.hpp"
#include "Shell/Flattening.hpp"
#include "Shell/Skolem.hpp"
#include "Shell/Statistics.hpp"

#include "InductionCNF.hpp"

using namespace Lib;
using namespace Kernel;

namespace Shell {

void InductionCNF::clausify(FormulaUnit* unit, Stack<Clause*>& output)
{
  CALL("InductionCNF::clausify");

  _beingClausified = unit;

  Formula* f = unit->formula();

  ASS(_genClauses.empty());
  ASS(_queue.isEmpty());
  ASS(_occurrences.isEmpty());

  enqueue(f, POSITIVE);

  introduceGenClause(f);

  // process the generalized clauses until they contain only literals
  while(_queue.isNonEmpty()) {
    process(_queue.pop_front());
  }

  for (SPGenClause gc : _genClauses) {
    output.push(toClause(gc));
  }

  _genClauses.clear();
  _varSorts.reset();
  _collectedVarSorts = false;
  _freeVars.reset();

  ASS(_queue.isEmpty());
  ASS(_occurrences.isEmpty());
}

void InductionCNF::process(JunctionFormula *g, Occurrences &occurrences, SIGN s)
{
  CALL("InductionCNF::process(JunctionFormula*)");

  FormulaList::Iterator fit(g->args());
  while (fit.hasNext()) {
    enqueue(fit.next(), s);
  }

  SIGN formulaSign = g->connective() == OR ? POSITIVE : NEGATIVE;

  while (occurrences.isNonEmpty()) {
    Occurrence occ = pop(occurrences);

    vvector<Formula*> fs;
    FormulaList::Iterator git(g->args());
    while (git.hasNext()) {
      fs.push_back(git.next());
    }

    if (s == formulaSign) {
      introduceExtendedGenClause(occ, fs);
    } else {
      for (const auto& f : fs) {
        introduceExtendedGenClause(occ, { f });
      }
    }
  }
}

void InductionCNF::process(BinaryFormula* g, Occurrences &occurrences, SIGN s)
{
  CALL("InductionCNF::process(BinaryFormula*)");

  ASS_EQ(g->connective(), IMP);

  Formula* lhs = g->left();
  Formula* rhs = g->right();

  enqueue(lhs, !s);
  enqueue(rhs, s);

  while (occurrences.isNonEmpty()) {
    Occurrence occ = pop(occurrences);

    if (s) {
      introduceExtendedGenClause(occ, { lhs, rhs });
    } else {
      introduceExtendedGenClause(occ, { lhs });
      introduceExtendedGenClause(occ, { rhs });
    }
  }
}

VarSet* InductionCNF::freeVars(Formula* g)
{
  CALL("InductionCNF::freeVars");

  VarSet* res;

  if (_freeVars.find(g,res)) {
    return res;
  }

  res = (VarSet*)VarSet::getFromIterator(FormulaVarIterator(g));

  _freeVars.insert(g,res);
  return res;
}

Term* InductionCNF::createSkolemTerm(unsigned var, VarSet* free)
{
  CALL("InductionCNF::createSkolemTerm");

  unsigned arity = free->size();

  if (!_collectedVarSorts) {
    SortHelper::collectVariableSorts(_beingClausified->formula(), _varSorts);
    _collectedVarSorts = true;
  }
  TermList rangeSort=_varSorts.get(var, AtomicSort::defaultSort());
  Stack<TermList> domainSorts;
  Stack<TermList> fnArgs;

  VarSet::Iterator vit(*free);
  while(vit.hasNext()) {
    unsigned uvar = vit.next();
    domainSorts.push(_varSorts.get(uvar, AtomicSort::defaultSort()));
    fnArgs.push(TermList(uvar, false));
  }

  // during induction no predicate Skolems should be present
  ASS_NEQ(rangeSort, AtomicSort::boolSort());
  unsigned fun = Skolem::addSkolemFunction(arity, domainSorts.begin(), rangeSort, var);
  env.statistics->skolemFunctions++;
  if(_beingClausified->derivedFromGoal()){
    env.signature->getFunction(fun)->markInGoal();
  }
  // env.signature->getFunction(fun)->markInductionSkolem();
  return Term::create(fun, arity, fnArgs.begin());
}

/**
 * Update the bindings of a generalized clause
 * in which a quantified formula g = (Quant Vars.Inner)
 * is being replaced by Inner. Each variable in Vars
 * will get a new binding. We try not to introduce
 * a new Skolem function unless it is necessary
 * so we cache results from skolemising previous
 * occurrences of g.
 */
void InductionCNF::skolemise(QuantifiedFormula* g)
{
  CALL("InductionCNF::skolemise");

  VarSet* frees = freeVars(g);

  Stack<unsigned> toSubtract;
  Stack<unsigned> toAddOnTop;

  for (unsigned i = 0; i < frees->size(); i++) {
    TermList t;
    if (_globalSubst.findBinding((*frees)[i], t)) {
      if (t.isTerm()) {
        toSubtract.push((*frees)[i]);  // because it's, in fact, bound
        VariableIterator vit(t);
        while (vit.hasNext()) {        // but depends on these free vars from above
          TermList t = vit.next();
          ASS(t.isVar());
          toAddOnTop.push(t.var());
        }
      }
    }
  }

  VarSet* boundVars = VarSet::getFromIterator(Stack<unsigned>::Iterator(toSubtract));
  VarSet* boundsDeps = VarSet::getFromIterator(Stack<unsigned>::Iterator(toAddOnTop));

  VarSet* unboundFreeVars = frees->subtract(boundVars)->getUnion(boundsDeps);

  VList::Iterator vs(g->vars());
  while (vs.hasNext()) {
    unsigned var = vs.next();
    _globalSubst.bind(var, createSkolemTerm(var, unboundFreeVars));
  }
}

void InductionCNF::process(QuantifiedFormula* g, Occurrences &occurrences, SIGN s)
{
  CALL("InductionCNF::process(QuantifiedFormula*)");

  // In the skolemising polarity introduce new skolems as you go
  // each occurrence may need a new set depending on bindings,
  // but let's try to share as much as possible
  Occurrences::Iterator occit(occurrences);
  while (occit.hasNext()) {
    Occurrence occ = occit.next();
    if ((s == POSITIVE) == (g->connective() == EXISTS)) {
      skolemise(g);
    } else {
      VList::Iterator vs(g->vars());
      while (vs.hasNext()) {
        unsigned var = vs.next();
        TermList tmp;
        if (_globalSubst.findBinding(var,tmp)) {
          ASS_EQ(var,tmp.var());
        } else {
          _globalSubst.bind(var, TermList(var, false));
        }
      }
    }
  }

  // Note that the formula under quantifier reuses the quantified formula's occurrences
  enqueue(g->qarg(), s, occurrences);

  // Correct all the GenClauses to mention qarg instead of g
  occurrences.replaceBy(g->qarg());
}

void InductionCNF::process(Formula* g)
{
  CALL("InductionCNF::process");
  Occurrences occurrences;
  ALWAYS(_occurrences.pop(g,occurrences));
  SIGN s = _signs.get(g);

  switch (g->connective()) {
    case AND:
    case OR:
      process(static_cast<JunctionFormula*>(g), occurrences, s);
      break;

    case IMP:
      process(static_cast<BinaryFormula*>(g), occurrences, s);
      break;

    case FORALL:
    case EXISTS:
      process(static_cast<QuantifiedFormula*>(g),occurrences, s);
      break;

    case LITERAL:
      ASS(g->literal()->shared());
      break;

    default:
      ASSERTION_VIOLATION_REP(g->toString());
  }
}

Clause* InductionCNF::toClause(SPGenClause gc)
{
  CALL("InductionCNF::toClause");

  Stack<Literal*> properLiterals;

  auto lit = gc->genLiterals();
  while (lit.hasNext()) {
    Formula* g = lit.next();

    ASS_EQ(g->connective(), LITERAL);
    ASS_REP(g->literal()->shared(), g->toString());

    auto l = g->literal()->apply(_globalSubst);
    if (!_signs.get(g)) {
      l = Literal::complementaryLiteral(l);
    }

    properLiterals.push(l);
  }

  Clause* clause = new(gc->_size) Clause(gc->_size,FormulaTransformation(InferenceRule::CLAUSIFY,_beingClausified));
  for (int i = gc->_size - 1; i >= 0; i--) {
    (*clause)[i] = properLiterals[i];
  }

  return clause;
}

}
