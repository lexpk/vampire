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
 * @file Intuitionistic.cpp
 * Implements transformations for expressing intuitionistic semantics.
 */

#include "Lib/Environment.hpp"

#include "Indexing/TermSharing.hpp"

#include "Kernel/Inference.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/FormulaVarIterator.hpp"

#include "Lib/List.hpp"

#include "Shell/Options.hpp"

#include "Intuitionistic.hpp"

using namespace Kernel;
using namespace Shell;


/**
 * Returns the axioms encoding intuitionistic semantics.
 * @warning the problem must be first-order
 */
void Intuitionistic::intuitionistic(Problem& prb)
{
  CALL("Intuitionistic::intuitionistic(Problem& prb)");

  //increase the arity of each predicate (except equality, which is i=0) by 1
  unsigned predicates = env.signature->predicates();
  for (unsigned i = 1; i < predicates; i++) {
    env.signature->addPredicate(env.signature->predicateName(i), env.signature->predicateArity(i) + 1);
  }

  unsigned existsPredicate = env.signature->addPredicate(existencePredicateName,2);
  unsigned kripkePartialOrder = env.signature->addPredicate(kripkePartialOrderName,2);

  UnitList*& units = prb.units();
  UnitList::DelIterator us(units);
  while (us.hasNext()) {
    Unit* u = us.next();
    Unit* res;
    Formula* formula = u->getFormula();
    unsigned varCnt = 0;
    FormulaVarIterator freeVariableIterator = FormulaVarIterator(formula);
    while (freeVariableIterator.hasNext()) {
      unsigned var = freeVariableIterator.next();
      if (var >= varCnt) {
        varCnt = var + 1;
      }
    }
    VList::Iterator boundVariableIterator = VList::Iterator(formula->boundVariables());
    while (boundVariableIterator.hasNext()) {
      unsigned var = boundVariableIterator.next();
      if (var >= varCnt) {
        varCnt = var + 1;
      }
    }
    Formula* f;
    if (u->inference().rule() == InferenceRule::NEGATED_CONJECTURE) {
      VList* vl = VList::empty();
      VList::push(varCnt, vl);
      f = intuitionistic(formula->uarg(), varCnt, kripkePartialOrder, existsPredicate);
      SList* ss = SList::empty();
      f = new QuantifiedFormula(FORALL, vl, ss, f);
      f = new NegatedFormula(f);
    } else {
      f = intuitionistic(formula, varCnt, kripkePartialOrder, existsPredicate);
    }
    f->label(formula->getLabel());
    res = new FormulaUnit(f, NonspecificInference1(InferenceRule::KRIPKE_SEMANTICS_FORMULA, u));

    if (env.options->showPreprocessing()) {
      env.beginOutput();
      env.out() << "[PP] kripke semantics in: " << u->toString() << endl;
      env.out() << "[PP] kripke semantics out: " << res->toString() << endl;
      env.endOutput();
    }
    us.replace(res);
  }

  FormulaUnit* partialOrderUnit = kripkePartialOrderAxiomatization(kripkePartialOrder);
  UnitList::push(partialOrderUnit, prb.units());

  FormulaUnit* existsUnit = existenceAxiomatization(existsPredicate);
  UnitList::push(existsUnit, prb.units());

  if (env.options->showPreprocessing()) {
    env.beginOutput();
    env.out() << "[PP] kripke partial order: " << partialOrderUnit->toString() << endl;
    env.out() << "[PP] existence: " << existsUnit->toString() << endl;
    env.endOutput();
  }
} // INTUITIONISTIC::intuitionistic(Problem&)


Formula* Intuitionistic::intuitionistic(Formula* f, unsigned varCnt, unsigned kripkePartialOrder, unsigned existsPredicate)
{
  CALL("Intuitionistic::intuitionistic(Formula*)");

  switch (f->connective()) {
    case LITERAL:
      {
        Formula* atom = new AtomicFormula(intuitionistic(f->literal(), varCnt+1)); 
        TermList x(varCnt, false);
        TermList y(varCnt+1, false);
        Literal* xleqy = Literal::create2(kripkePartialOrder, true, x, y);
        Formula* xly = new AtomicFormula(xleqy);
        Formula* impl = new BinaryFormula(IMP, xly, atom);
        VList* vars = VList::empty();
        VList::push(varCnt+1, vars);
        SList* sorts = SList::empty();
        Formula* res = new QuantifiedFormula(FORALL, vars, sorts, impl);
        return res;
      }
    case AND:
    case OR:
      {
        FormulaList* newArgs = FormulaList::empty();
        FormulaList::Iterator it(f->args());
        while (it.hasNext()) {
          Formula* arg = it.next();
          FormulaList::push(intuitionistic(arg, varCnt, kripkePartialOrder, existsPredicate), newArgs);
        }
        return new JunctionFormula(f->connective(), newArgs);
      }
    case IMP:
    case IFF:
      {
        TermList x(varCnt, false);
        TermList y(varCnt+1, false);
        Literal* xleqy = Literal::create2(kripkePartialOrder, true, x, y);
        Formula* xly = new AtomicFormula(xleqy);
        VList* vars = VList::empty();
        VList::push(varCnt+1, vars);
        Formula* left = intuitionistic(f->left(), varCnt+1, kripkePartialOrder, existsPredicate);
        Formula* right = intuitionistic(f->right(), varCnt+1, kripkePartialOrder, existsPredicate);
        Formula* arg = new BinaryFormula(f->connective(), left, right);
        Formula* arg2 = new BinaryFormula(IMP, xly, arg);
        SList* ss = SList::empty();
        Formula* result = new QuantifiedFormula(FORALL, vars, ss, arg2);
        return result;
      }
    case XOR:
      {
        TermList x(varCnt, false);
        TermList y(varCnt+1, false);
        TermList z(varCnt+2, false);
        Literal* xleqy = Literal::create2(kripkePartialOrder, true, x, y);
        Literal* yleqz = Literal::create2(kripkePartialOrder, true, y, z);
        Formula* xly = new AtomicFormula(xleqy);
        Formula* ylz = new AtomicFormula(yleqz);
        VList* varsForall0 = VList::empty();
        VList::push(varCnt+1, varsForall0);
        VList* varsForall1 = VList::empty();
        VList::push(varCnt+2, varsForall1);
        Formula* left = intuitionistic(f->left(), varCnt+2, kripkePartialOrder, existsPredicate);
        Formula* right = intuitionistic(f->right(), varCnt+2, kripkePartialOrder, existsPredicate);
        Formula* arg = new BinaryFormula(IFF, left, right);
        Formula* arg2 = new BinaryFormula(IMP, ylz, arg);
        SList* ss = SList::empty();
        Formula* arg3 = new QuantifiedFormula(FORALL, varsForall1, ss, arg2);
        Formula* arg4 = new NegatedFormula(arg3);
        Formula* arg5 = new BinaryFormula(IMP, xly, arg4);
        Formula* arg6 = new QuantifiedFormula(FORALL, varsForall0, ss, arg5);
        return arg6;
      }
    case FORALL:
      {
        TermList x(varCnt, false);
        TermList y(varCnt+1, false);
        VList* vars = f->vars();
        
        FormulaList* conditions = FormulaList::empty();
        VList::Iterator it(vars);
        while (it.hasNext()) {
          TermList var(it.next(), false);
          Literal* l = Literal::create2(existsPredicate, true, var, y);
          AtomicFormula* cond = new AtomicFormula(l);
          FormulaList::push(cond, conditions);
        }
        VList::push(varCnt+1, vars);
        Literal* xleqy = Literal::create2(kripkePartialOrder, true, x, y);
        Formula* xly = new AtomicFormula(xleqy);
        FormulaList::push(xly, conditions);
        Formula* condition = new JunctionFormula(AND, conditions);

        Formula* arg = intuitionistic(f->qarg(), varCnt+1, kripkePartialOrder, existsPredicate);
        Formula* arg2 = new BinaryFormula(IMP, condition, arg);
        SList* ss = SList::empty();
        QuantifiedFormula* result = new QuantifiedFormula(f->connective(), vars, ss, arg2);
        return result;
      }
    case EXISTS:
      {
        TermList x(varCnt, false);
        FormulaList* args = FormulaList::empty();
        VList::Iterator it(f->vars());
        while (it.hasNext()) {
          TermList var(it.next(), false);
          Literal* l = Literal::create2(existsPredicate, true, var, x);
          Formula* cond = new AtomicFormula(l);
          FormulaList::push(cond, args);
        }
        Formula* arg = intuitionistic(f->qarg(), varCnt, kripkePartialOrder, existsPredicate);
        FormulaList::push(arg, args);
        Formula* arg2 = new JunctionFormula(AND, args);
        SList* ss = SList::empty();
        QuantifiedFormula* result = new QuantifiedFormula(f->connective(), f->vars(), ss, arg2);
        return result;
      }
    case TRUE:
    case FALSE:
      return f;
    case NOT:
      {
        TermList x(varCnt, false);
        TermList y(varCnt+1, false);
        VList* vars = VList::empty();
        VList::push(varCnt+1, vars);
        Literal* xleqy = Literal::create2(kripkePartialOrder, true, x, y);
        Formula* xly = new AtomicFormula(xleqy);
        Formula* arg = intuitionistic(f->uarg(), varCnt+1, kripkePartialOrder, existsPredicate);
        Formula* arg2 = new NegatedFormula(arg);
        Formula* arg3 = new BinaryFormula(IMP, xly, arg2);
        SList* ss = SList::empty();
        QuantifiedFormula* result = new QuantifiedFormula(FORALL, vars, ss, arg3);
        return result;
      }
    case BOOL_TERM:
    case NAME:
    case NOCONN:
      ASSERTION_VIOLATION;
  }
  ASSERTION_VIOLATION;
} // INTUITIONISTIC::intuitionistic(Formula*)

Literal* Intuitionistic::intuitionistic(Literal* l, unsigned varCnt)
{
  CALL("Intuitionistic::intuitionistic(Literal*)");

  if (l->isEquality()) {
    return l;
  }
  
  unsigned arity = l->arity() + 1;
  unsigned functor = env.signature->getPredicateNumber(env.signature->predicateName(l->functor()), arity);
  TermList tl = TermList(arity*sizeof(size_t));
  TermList* newArgs = &tl;
  for (unsigned i = 0;i < arity - 1; i++) {
    newArgs[i] = l->termArg(i);
  }
  TermList x(varCnt, false);
  newArgs[arity-1] = x;
  Literal* lit = Literal::create(functor, arity, l->polarity(), l->isEquality(), newArgs);
  return lit;
} // INTUITIONISTIC::intuitionistic(Literal*)

FormulaUnit* Intuitionistic::kripkePartialOrderAxiomatization(unsigned kripkePartialOrder) {
  Literal* reflexivity = new(2) Literal(kripkePartialOrder,2,true,false);
  TermList x0(0, false);
  *reflexivity->nthArgument(0) = x0;
  *reflexivity->nthArgument(1) = x0;
  reflexivity = env.sharing->insert(reflexivity);
  Formula* refl = new AtomicFormula(reflexivity);
  
  Literal* symmetry0 = new(2) Literal(kripkePartialOrder,2,true,false);
  TermList x1(1, false);
  TermList x2(2, false);
  *symmetry0->nthArgument(0) = x1;
  *symmetry0->nthArgument(1) = x2;
  symmetry0 = env.sharing->insert(symmetry0);
  Literal* symmetry1 = new(2) Literal(kripkePartialOrder,2,true,false);
  *symmetry1->nthArgument(0) = x2;
  *symmetry1->nthArgument(1) = x1;
  symmetry1 = env.sharing->insert(symmetry1);
  FormulaList* symmetry = FormulaList::empty();
  Formula* symm0 = new AtomicFormula(symmetry0);
  Formula* symm1 = new AtomicFormula(symmetry1);
  FormulaList::push(symm0, symmetry);
  FormulaList::push(symm1, symmetry);
  Formula* symm = new JunctionFormula(OR, symmetry);

  Literal* transitivity0 = new(2) Literal(kripkePartialOrder,2,false,false);
  TermList x3(3, false);
  TermList x4(4, false);
  TermList x5(5, false);
  *transitivity0->nthArgument(0) = x3;
  *transitivity0->nthArgument(1) = x4;
  transitivity0 = env.sharing->insert(transitivity0);
  Literal* transitivity1 = new(2) Literal(kripkePartialOrder,2,false,false);
  *transitivity1->nthArgument(0) = x4;
  *transitivity1->nthArgument(1) = x5;
  transitivity1 = env.sharing->insert(transitivity1);
  Literal* transitivity2 = new(2) Literal(kripkePartialOrder,2,true,false);
  *transitivity2->nthArgument(0) = x3;
  *transitivity2->nthArgument(1) = x5;
  transitivity2 = env.sharing->insert(transitivity2);
  Formula* trans0 = new AtomicFormula(transitivity0);
  Formula* trans1 = new AtomicFormula(transitivity1);
  Formula* trans2 = new AtomicFormula(transitivity2);
  FormulaList* transitivity = FormulaList::empty();
  FormulaList::push(trans0, transitivity);
  FormulaList::push(trans1, transitivity);
  FormulaList::push(trans2, transitivity);
  Formula* trans = new JunctionFormula(OR, transitivity);

  FormulaList* partialOrder = FormulaList::empty();
  FormulaList::push(refl, partialOrder);
  FormulaList::push(symm, partialOrder);
  FormulaList::push(trans, partialOrder);
  Formula* po = new JunctionFormula(AND, partialOrder);

  return new FormulaUnit(po, TheoryAxiom(InferenceRule::KRIPKE_PO));
}// INTUITIONISTIC::kripkePartialOrder(unsigned)

FormulaUnit* Intuitionistic::existenceAxiomatization(unsigned existencePredicate) {
  unsigned functionCnt = env.signature->functions();
  FormulaList* axioms = FormulaList::empty();
  for(unsigned f=0; f<functionCnt; f++) {
    unsigned arity = env.signature->functionArity(f);
    switch (arity) {
      case 0:
      {
        TermList world(arity, false);
        Term* constant = Term::createConstant(f);
        TermList arg = TermList(constant);
        Literal* lit = Literal::create2(existencePredicate, true, arg, world);
        Formula* result = new AtomicFormula(lit);
        FormulaList::push(result, axioms);
        break;
      }
      case 1:
      {
        TermList world(arity, false);
        TermList x(0, false);
        Literal* condLit = Literal::create2(existencePredicate, true, x, world);
        Formula* cond = new AtomicFormula(condLit);
        Term* t = Term::create(f, arity, &x);
        TermList arg = TermList(t);
        Literal* conclLit = Literal::create2(existencePredicate, true, arg, world);
        Formula* concl = new AtomicFormula(conclLit);
        Formula* result = new BinaryFormula(IMP, cond, concl);
        FormulaList::push(result, axioms);
        break;
      }
      default:
      { 
        FormulaList* conditions = FormulaList::empty();
        TermList world(arity, false);

        Term* s = new(arity) Term;
        s->makeSymbol(f,arity);
        TermList* ss = s->args();

        for (unsigned j = 0; j < arity; j++) {
          TermList x(j, false);

          Literal* l = Literal::create2(existencePredicate, true, x, world);
          AtomicFormula* cond = new AtomicFormula(l);
          FormulaList::push(cond, conditions);

          *ss = TermList(j, false);
          --ss;
        }
        Formula* condition = new JunctionFormula(AND, conditions);

        s = env.sharing->insert(s);
        TermList arg = TermList(s);
        Literal* lit = Literal::create2(existencePredicate, true, arg, world);
        Formula* conclusion = new AtomicFormula(lit);

        Formula* result = new BinaryFormula(IMP, condition, conclusion);
        FormulaList::push(result, axioms);
      }
    }
  }
  Formula* axiomatization;
  FormulaUnit* result;
  TermList x(0, false);
  TermList world(1, false);
  VList* varsExist = VList::empty();
  VList::push(x.var(), varsExist);
  VList* varsForall = VList::empty();
  VList::push(world.var(), varsForall);
  SList* ss = SList::empty();
  Formula* atom = new AtomicFormula(Literal::create2(existencePredicate, true, x, world));
  Formula* forall = new QuantifiedFormula(FORALL, varsForall, ss, atom);
  Formula* exists = new QuantifiedFormula(EXISTS, varsExist, ss, forall);
  switch (functionCnt) {
    case 0:
      result = new FormulaUnit(exists, TheoryAxiom(InferenceRule::KRIPKE_EXISTENCE));
      break;
    default:
      FormulaList::push(exists, axioms);
      axiomatization = new JunctionFormula(AND, axioms);
      result = new FormulaUnit(axiomatization, TheoryAxiom(InferenceRule::KRIPKE_EXISTENCE));
  }
  return result;
}// INTUITIONISTIC::existenceAxiomatization(unsigned)

