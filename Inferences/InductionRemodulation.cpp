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
 * @file InductionRemodulation.cpp
 * Implements class InductionRemodulation.
 */

#include "Lib/Metaiterators.hpp"

#include "Kernel/SortHelper.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/TermIterators.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Options.hpp"

#include "InductionHelper.hpp"

#include "InductionRemodulation.hpp"
#include "InductionForwardRewriting.hpp"

namespace Inferences {

using namespace Lib;
using namespace Kernel;

TermList SingleOccurrenceReplacementIterator::Replacer::transformSubterm(TermList trm)
{
  CALL("SingleOccurrenceReplacementIterator::Replacer::transformSubterm");

  if (trm.isVar() || _matchCount > _i) {
    return trm;
  }
  if (trm.term() == _o && _i == _matchCount++) {
    return _r;
  }
  return trm;
}

Literal* SingleOccurrenceReplacementIterator::next()
{
  CALL("SingleOccurrenceReplacementIterator::next");
  ASS(hasNext());
  Replacer sor(_o, _r, _iteration++);
  return sor.transform(_lit);
}

void InductionRemodulation::attach(SaturationAlgorithm* salg)
{
  CALL("InductionRemodulation::attach");
  GeneratingInferenceEngine::attach(salg);
  _lhsIndex=static_cast<RemodulationLHSIndex*>(
	  _salg->getIndexManager()->request(REMODULATION_LHS_SUBST_TREE) );
  _termIndex=static_cast<RemodulationSubtermIndex*>(
	  _salg->getIndexManager()->request(REMODULATION_SUBTERM_INDEX) );
  _demLhsIndex=static_cast<DemodulationLHSIndex*>(
	  _salg->getIndexManager()->request(DEMODULATION_LHS_SUBST_TREE) );
}

void InductionRemodulation::detach()
{
  CALL("InductionRemodulation::detach");
  _demLhsIndex = 0;
  _salg->getIndexManager()->release(DEMODULATION_LHS_SUBST_TREE);
  _lhsIndex = 0;
  _salg->getIndexManager()->release(REMODULATION_LHS_SUBST_TREE);
  _termIndex = 0;
  _salg->getIndexManager()->release(REMODULATION_SUBTERM_INDEX);
  GeneratingInferenceEngine::detach();
}

struct ReverseLHSIteratorFn {
  ReverseLHSIteratorFn(Clause* cl) : _cl(cl) {}
  VirtualIterator<pair<Literal*, TermList>> operator()(pair<Literal*, TermList> arg)
  {
    CALL("ReverseLHSIteratorFn()");
    ASS(arg.first->isPositive());
    auto rhs = EqHelper::getOtherEqualitySide(arg.first, arg.second);
    if (!termHasAllVarsOfClause(rhs, _cl) || !hasTermToInductOn(arg.second.term(), arg.first)) {
      return VirtualIterator<pair<Literal*, TermList>>::getEmpty();
    }
    return pvi(getSingletonIterator(make_pair(arg.first,rhs)));
  }
private:
  Clause* _cl;
};

ClauseIterator InductionRemodulation::generateClauses(Clause* premise)
{
  CALL("InductionRemodulation::generateClauses");
  ClauseIterator res1 = ClauseIterator::getEmpty();

  if (InductionHelper::isInductionClause(premise))
  {
    // forward result
    res1 = pvi(iterTraits(premise->iterLits())
      .filter([this,premise](Literal* lit) {
        return shouldRewriteEquality(lit, premise, _salg->getOrdering()) || InductionHelper::isInductionLiteral(lit);
      })
      .flatMap([](Literal* lit) {
        NonVariableNonTypeIterator it(lit);
        return pvi( pushPairIntoRightIterator(lit, getUniquePersistentIteratorFromPtr(&it)) );
      })
      .flatMap([this](pair<Literal*, TermList> arg) {
        return pvi( pushPairIntoRightIterator(arg, _lhsIndex->getUnifications(arg.second, true)) );
      })
      .flatMap([this, premise](pair<pair<Literal*, TermList>, TermQueryResult> arg) {
        TermQueryResult& qr = arg.second;
        return perform(premise, arg.first.first, arg.first.second,
          qr.clause, qr.literal, qr.term, qr.substitution, true);
      }));
  }

  // backward result
  ClauseIterator res2 = pvi(iterTraits(premise->iterLits())
    .flatMap(EqHelper::LHSIteratorFn(_salg->getOrdering()))
    .flatMap(ReverseLHSIteratorFn(premise))
    .flatMap([this](pair<Literal*, TermList> arg) {
      return pvi( pushPairIntoRightIterator(arg, _termIndex->getUnifications(arg.second, true)) );
    })
    .flatMap([this, premise](pair<pair<Literal*, TermList>, TermQueryResult> arg) {
      TermQueryResult& qr = arg.second;
      return perform(qr.clause, qr.literal, qr.term,
        premise, arg.first.first, arg.first.second, qr.substitution, false);
    }));

  return pvi(iterTraits(getConcatenatedIterator(res1,res2))
    .filter(NonzeroFn())
    .timeTraced("induction remodulation"));
}

vset<unsigned> getSkolems(Literal* lit) {
  vset<unsigned> res;
  NonVariableNonTypeIterator it(lit);
  while (it.hasNext()) {
    auto trm = it.next();
    if (env.signature->getFunction(trm.term()->functor())->skolem()) {
      res.insert(trm.term()->functor());
    }
  }
  return res;
}

TermList getSideRewritten(Literal* lit, Literal* orig) {
  ASS_REP(lit->isEquality(), lit->toString());
  ASS_REP(orig->isEquality(), orig->toString());
  ASS_NEQ(lit,orig);
  auto lhsNew = *lit->nthArgument(0);
  auto rhsNew = *lit->nthArgument(1);
  auto lhsOld = *orig->nthArgument(0);
  auto rhsOld = *orig->nthArgument(1);
  TermList rwSide;
  TermList other;
  if (lhsNew == lhsOld || rhsNew == lhsOld) {
    return rhsOld;
  }
  ASS(lhsNew == rhsOld || rhsNew == rhsOld);
  return lhsOld;
}

TermList getArgumentRewritten(Literal* lit, Literal* orig) {
  ASS(!lit->isEquality());
  ASS(!orig->isEquality());
  ASS_NEQ(lit,orig);
  ASS_EQ(lit->functor(),orig->functor());
  for (unsigned i = 0; i < lit->arity(); i++) {
    if (lit->nthArgument(i) != orig->nthArgument(i)) {
      return *lit->nthArgument(i);
    }
  }
  ASSERTION_VIOLATION;
}

bool greaterSideRewritten(Literal* lit, Literal* orig, Ordering& ord) {
  auto rwSide = getSideRewritten(lit, orig);
  return ord.compare(rwSide, EqHelper::getOtherEqualitySide(orig, rwSide)) == Ordering::GREATER;
}

void InductionRemodulation::output()
{
  CALL("InductionRemodulation::output");
  auto s = iterTraits(_eqs.items()).collect<Stack>();
  std::sort(s.begin(),s.end(),[](pair<Clause*,unsigned> kv1, pair<Clause*,unsigned> kv2) {
    return kv1.second < kv2.second;
  });
  cout << "eqs" << endl;
  for (const auto& kv : s) {
    cout << *kv.first << " " << kv.second << endl;
  }
  cout << "end " << endl << endl;
}

ClauseIterator InductionRemodulation::perform(
    Clause* rwClause, Literal* rwLit, TermList rwTerm,
    Clause* eqClause, Literal* eqLit, TermList eqLHS,
    ResultSubstitutionSP subst, bool eqIsResult)
{
  CALL("InductionRemodulation::perform");
  // we want the rwClause and eqClause to be active
  ASS(rwClause->store()==Clause::ACTIVE);
  ASS(eqClause->store()==Clause::ACTIVE);

  vset<unsigned> eqSkolems = getSkolems(eqLit);
  if (!eqSkolems.empty()) {
    vset<unsigned> rwSkolems = getSkolems(rwLit);
    vset<unsigned> is;
    set_intersection(eqSkolems.begin(), eqSkolems.end(), rwSkolems.begin(), rwSkolems.end(), inserter(is, is.end()));
    if (is != eqSkolems) {
      return ClauseIterator::getEmpty();
    }
  }

  // cout << "performRemodulation with " << *rwClause << " and " << *eqClause << endl
  //   << "rwLit " << *rwLit << " eqLit " << *eqLit << endl
  //   << "rwTerm " << rwTerm << " eqLHS " << eqLHS << endl
  //   // << "subst " << endl << subst->tryGetRobSubstitution()->toString() << endl
  //   << "eqIsResult " << eqIsResult << endl;

  if (eqLHS.isVar()) {
    TermList eqLHSsort = SortHelper::getEqualityArgumentSort(eqLit);
    TermList tgtTermSort = SortHelper::getTermSort(rwTerm, rwLit);
    if (eqLHSsort != tgtTermSort) {
      return ClauseIterator::getEmpty();
    }
  }

  TermList tgtTerm = EqHelper::getOtherEqualitySide(eqLit, eqLHS);
  TermList tgtTermS = subst->applyTo(tgtTerm, eqIsResult);
  TermList rwTermS = subst->applyTo(rwTerm, !eqIsResult);
  Literal* rwLitS = subst->applyTo(rwLit, !eqIsResult);

  auto comp = _salg->getOrdering().compare(tgtTermS,rwTermS);
  if (comp != Ordering::GREATER && comp != Ordering::GREATER_EQ) {
    // ASS_NEQ(comp, Ordering::INCOMPARABLE);
    return ClauseIterator::getEmpty();
  }

  return pvi(iterTraits(vi(new SingleOccurrenceReplacementIterator(rwLitS, rwTermS.term(), tgtTermS)))
    .map([this,eqClause,rwClause,eqLit,rwLit,rwLitS,eqIsResult,subst](Literal* tgtLitS) -> Clause* {
      if(EqHelper::isEqTautology(tgtLitS)) {
        return nullptr;
      }
      if (!InductionHelper::isInductionLiteral(rwLit) && !greaterSideRewritten(tgtLitS, rwLitS, _salg->getOrdering())) {
        return nullptr;
      }
      auto lastRewritten = rwClause->inference().rule() == InferenceRule::INDUCTION_REMODULATION ? rwClause->getLastRewrittenTerm() : nullptr;
      static unsigned skipped = 0;
      if (lastRewritten) {
        // cout << *rwClause << *lastRewritten << endl;
        // TODO the switch between forward and backward has to be signaled somehow
        // ASS(rwClause->inference().rule() != InferenceRule::INDUCTION_FORWARD_REWRITING);
        auto rwArg = rwLit->isEquality() ? getSideRewritten(tgtLitS, rwLitS) : getArgumentRewritten(tgtLitS, rwLitS);
        auto lastRewrittenS = subst->applyTo(TermList(lastRewritten), eqIsResult);
        auto comp = _salg->getOrdering().compare(lastRewrittenS, rwArg);
        ASS_NEQ(comp, Ordering::Result::INCOMPARABLE); // terms are ground here
        if (comp == Ordering::Result::LESS || comp == Ordering::Result::LESS_EQ) {
          skipped++;
          // if (skipped % 100 == 0) {
          //   cout << "skipped " << skipped << endl;
          // }
          return nullptr;
        }
      }

      unsigned rwLength = rwClause->length();
      unsigned eqLength = eqClause->length();
      unsigned newLength = rwLength + (eqLength - 1);
      Inference inf(GeneratingInference2(InferenceRule::INDUCTION_REMODULATION, rwClause, eqClause));
      Clause* newCl = new(newLength) Clause(newLength, inf);

      (*newCl)[0] = tgtLitS;
      int next = 1;
      for(unsigned i=0;i<rwLength;i++) {
        Literal* curr=(*rwClause)[i];
        if(curr!=rwLit) {
          Literal *currAfter = subst->applyTo(curr,!eqIsResult);
          if (EqHelper::isEqTautology(currAfter)) {
            newCl->destroy();
            return nullptr;
          }

          (*newCl)[next++] = currAfter;
        }
      }

      for (unsigned i = 0; i < eqLength; i++) {
        Literal *curr = (*eqClause)[i];
        if (curr != eqLit) {
          Literal *currAfter = subst->applyTo(curr,eqIsResult);

          if (EqHelper::isEqTautology(currAfter)) {
            newCl->destroy();
            return nullptr;
          }

          (*newCl)[next++] = currAfter;
        }
      }
      ASS_EQ(next, newLength);

      env.statistics->inductionRemodulation++;
      auto ptr = _eqs.findPtr(eqClause);
      if (!ptr) {
        _eqs.insert(eqClause, 1);
      } else {
        (*ptr)++;
      }
      // cout << "result " << *newCl << endl << endl;
      newCl->markBackwardParamodulated();
      Term* rewritten = (rwLitS->isEquality() ? getSideRewritten(tgtLitS, rwLitS) : getArgumentRewritten(tgtLitS, rwLitS)).term();
      newCl->setLastRewrittenTerm(rewritten);
      return newCl;
    }));
}

SimplifyingGeneratingInference::ClauseGenerationResult InductionSGIWrapper::generateSimplify(Clause* premise)
{
  CALL("InductionSGIWrapper::generateSimplify");
  static unsigned cnt = 0;
  cnt++;
  if (cnt % 1000 == 0) {
    // _inductionRemodulation->output();
    // _inductionForwardRewriting->output();
  }
  if (!premise->isBackwardParamodulated() && !premise->isForwardParamodulated()) {
    return _generator->generateSimplify(premise);
  }
  ASS(!premise->isBackwardParamodulated() || !premise->isForwardParamodulated());
  auto it = iterTraits(ClauseIterator::getEmpty());
  if (premise->isForwardParamodulated()) {
    it.concat(_inductionForwardRewriting->generateClauses(premise));
  }
  it.concat(_induction->generateClauses(premise), _inductionRemodulation->generateClauses(premise));
  return ClauseGenerationResult {
    .clauses = pvi(it),
    .premiseRedundant = false,
  };
}

}