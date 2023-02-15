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
 * @file InductionRewriting.cpp
 * Implements class InductionRewriting.
 */

#include "Lib/Metaiterators.hpp"

#include "Kernel/RobSubstitution.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/TermIterators.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Options.hpp"

#include "InductionHelper.hpp"

#include "InductionRewriting.hpp"

namespace Inferences {

using namespace Lib;
using namespace Kernel;

// iterators and filters

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


bool isTermViolatingBound(Term* bound, TermList t, Ordering& ord, bool downward)
{
  CALL("isTermViolatingBound");
  if (!bound) {
    return false;
  }
  auto comp = ord.compare(TermList(bound), TermList(t));
  if (comp == Ordering::Result::EQUAL) {
    static unsigned cnt = 0;
    cnt++;
    if (cnt % 1000 == 0) {
      cout << "equal " << cnt << endl;
    }
  }
  if (downward) {
    if (comp == Ordering::Result::LESS || comp == Ordering::Result::LESS_EQ) {
      return true;
    }
  } else {
    if (comp == Ordering::Result::GREATER || comp == Ordering::Result::GREATER_EQ) {
      return true;
    }
  }
  return false;
}

LitArgPairIter getIterator(Ordering& ord, Clause* premise, bool downward)
{
  CALL("InductionRewriting::getIterator");
  Term* bound;
  if (downward) {
    bound = premise->getRewritingUpperBound();
  } else {
    bound = premise->getRewritingLowerBound();
  }
  return pvi(iterTraits(premise->iterLits())
    .flatMap([](Literal* lit) {
      return pvi(pushPairIntoRightIterator(lit, termArgIter(lit)));
    })
    // filter out ones violating the bound
    .filter([bound,&ord,downward](LitArgPair kv) {
      return !isTermViolatingBound(bound, kv.second, ord, downward);
    }));
}

bool isClauseRewritable(const Options& opt, Clause* premise, bool downward)
{
  CALL("InductionRewriting::isClauseRewritable");
  if (premise->isPureTheoryDescendant()) {
    return false;
  }
  if (!downward && (!opt.nonUnitInduction() || opt.splitting()) &&
    (!InductionHelper::isInductionClause(premise) || !InductionHelper::isInductionLiteral((*premise)[0])))
  {
    return false;
  }
  return true;
}

bool canClauseRewrite(Clause* premise)
{
  CALL("InductionRewriting::canClauseRewrite");
  if (premise->isPureTheoryDescendant()) {
    return false;
  }
  return true;
}

bool areEqualitySidesOriented(TermList lhs, TermList rhs, Ordering& ord, bool downward)
{
  CALL("InductionRewriting::areTermsOriented");

  auto comp = ord.compare(rhs,lhs);
  if (downward && Ordering::isGorGEorE(comp)) {
    return false;
  }
  if (!downward && !Ordering::isGorGEorE(comp)) {
    return false;
  }
  return true;
}

bool canUseLHSForRewrite(LitArgPair kv, Clause* premise, bool downward)
{
  CALL("InductionRewriting::canUseLHSForRewrite");
  auto lhs = kv.second;
  // cannot yet handle new variables that pop up
  if (iterTraits(premise->getVariableIterator())
      .any([&lhs](unsigned v) {
        return !lhs.containsSubterm(TermList(v, false));
      }))
  {
    return false;
  }
  // lhs contains only things we cannot induct on
  auto lit = kv.first;
  auto rhs = EqHelper::getOtherEqualitySide(lit, TermList(lhs));
  if (!downward && premise->length() == 1 && rhs.isTerm() && !hasTermToInductOn(rhs.term(), lit)) {
    return false;
  }
  return true;
}

bool canUseTermForRewrite(Clause* premise, LitArgPair kv, Ordering& ord, bool downward)
{
  CALL("InductionRewriting::canUseTermForRewrite");
  if (downward && !kv.first->ground() && kv.first->isEquality() &&
    !areEqualitySidesOriented(
      TermList(kv.second),
      EqHelper::getOtherEqualitySide(kv.first, TermList(kv.second)),
      ord, downward))
  {
    return false;
  }
  return true;
}

LitArgPairIter InductionRewriting::getTermIterator(Clause* premise, const Options& opt, Ordering& ord, bool downward)
{
  CALL("InductionRewriting::getTermIterator");
  if (!isClauseRewritable(opt, premise, downward)) {
    return LitArgPairIter::getEmpty();
  }
  return pvi(iterTraits(getIterator(ord, premise, downward))
    .filter([premise,&ord,downward](LitArgPair kv) {
      return canUseTermForRewrite(premise, kv, ord, downward);
    }));
}

LitArgPairIter InductionRewriting::getLHSIterator(Clause* premise, const Options& opt, Ordering& ord, bool downward)
{
  CALL("InductionRewriting::getLHSIterator");
  if (!canClauseRewrite(premise)) {
    return LitArgPairIter::getEmpty();
  }
  return pvi(iterTraits(getIterator(ord, premise, downward))
    .filter([&opt](LitArgPair kv) {
      return opt.inductionEquationalLemmaGeneration()==Options::LemmaGeneration::ALL || kv.first->isForLemmaGeneration();
    })
    .filter([&ord, downward](LitArgPair kv) {
      auto lit = kv.first;
      if (!lit->isEquality() || lit->isNegative()) {
        return false;
      }
      auto lhs = kv.second;
      return areEqualitySidesOriented(lhs, EqHelper::getOtherEqualitySide(lit, lhs), ord, downward);
    })
    .filter([premise,downward](LitArgPair kv) {
      return canUseLHSForRewrite(kv, premise, downward);
    }));
}

// inference

void InductionRewriting::attach(SaturationAlgorithm* salg)
{
  CALL("InductionRewriting::attach");
  GeneratingInferenceEngine::attach(salg);
  _lhsIndex=static_cast<TermIndex*>(
	  _salg->getIndexManager()->request(_downward ? FORWARD_REWRITING_LHS_INDEX : BACKWARD_REWRITING_LHS_INDEX) );
  _termIndex=static_cast<TermIndex*>(
	  _salg->getIndexManager()->request(_downward ? FORWARD_REWRITING_SUBTERM_INDEX : BACKWARD_REWRITING_SUBTERM_INDEX) );
}

void InductionRewriting::detach()
{
  CALL("InductionRewriting::detach");
  _termIndex = 0;
  _salg->getIndexManager()->release(_downward ? FORWARD_REWRITING_SUBTERM_INDEX : BACKWARD_REWRITING_SUBTERM_INDEX);
  _lhsIndex = 0;
  _salg->getIndexManager()->release(_downward ? FORWARD_REWRITING_LHS_INDEX : BACKWARD_REWRITING_LHS_INDEX);
  GeneratingInferenceEngine::detach();
}

ClauseIterator InductionRewriting::generateClauses(Clause* premise)
{
  CALL("InductionRewriting::generateClauses");
  auto& ord = _salg->getOrdering();
  auto& opt = _salg->getOptions();

  // forward result
  auto fwRes = iterTraits(getTermIterator(premise, opt, ord, _downward))
    .flatMap([](LitArgPair kv) {
      if (kv.second.isVar()) {
        return VirtualIterator<pair<LitArgPair, TermList>>::getEmpty();
      }
      NonVariableNonTypeIterator it(kv.second.term(), true);
      return pvi( pushPairIntoRightIterator(kv, getUniquePersistentIteratorFromPtr(&it)) );
    })
    .flatMap([this](pair<LitArgPair, TermList> arg) {
      return pvi( pushPairIntoRightIterator(arg, _lhsIndex->getUnifications(arg.second, true)) );
    })
    .flatMap([this, premise](pair<pair<LitArgPair, TermList>, TermQueryResult> arg) {
      TermQueryResult& qr = arg.second;
      return perform(premise, arg.first.first.first, arg.first.first.second, arg.first.second,
        qr.clause, qr.literal, qr.term, qr.substitution, true);
    })
    .timeTraced(_downward ? "forward downward paramodulation" : "forward upward paramodulation");

  // backward result
  auto bwRes = iterTraits(getLHSIterator(premise, opt, ord, _downward))
    .flatMap([this](LitArgPair kv) {
      return pvi( pushPairIntoRightIterator(make_pair(kv.first, TermList(kv.second)), _termIndex->getUnifications(TermList(kv.second), true)) );
    })
    .flatMap([](pair<pair<Literal*, TermList>, TermQueryResult> arg) {
      return pvi( pushPairIntoRightIterator(arg, termArgIter(arg.second.literal)) );
    })
    .map([](pair<pair<pair<Literal*, TermList>, TermQueryResult>, TermList> arg) {
      return make_pair(make_pair(make_pair(arg.first.first.first, arg.second), arg.first.first.second), arg.first.second);
    })
    .flatMap([this, premise](pair<pair<LitArgPair, TermList>, TermQueryResult> arg) {
      TermQueryResult& qr = arg.second;
      return perform(qr.clause, qr.literal, arg.first.first.second, qr.term,
        premise, arg.first.first.first, arg.first.second, qr.substitution, false);
    })
    .timeTraced(_downward ? "backward downward paramodulation" : "backward upward paramodulation");

  return pvi(fwRes.concat(bwRes).filter(NonzeroFn()));
}

TermList getRewrittenTerm(Literal* oldLit, Literal* newLit) {
  // cout << *oldLit << " " << *newLit << endl;
  ASS_EQ(oldLit->functor(), newLit->functor());
  ASS_NEQ(newLit,oldLit);
  if (oldLit->commutative()) {
    auto lhsNew = *newLit->nthArgument(0);
    auto rhsNew = *newLit->nthArgument(1);
    auto lhsOld = *oldLit->nthArgument(0);
    auto rhsOld = *oldLit->nthArgument(1);
    if (lhsNew == lhsOld || rhsNew == lhsOld) {
      return rhsOld;
    }
    ASS(lhsNew == rhsOld || rhsNew == rhsOld);
    return lhsOld;
  } else {
    for (unsigned i = 0; i < oldLit->arity(); i++) {
      auto oldArg = *oldLit->nthArgument(i);
      auto newArg = *newLit->nthArgument(i);
      if (oldArg != newArg) {
        return oldArg;
      }
    }
    ASSERTION_VIOLATION;
  }
}

// bool greaterSideRewritten(Literal* lit, Literal* orig, Ordering& ord) {
//   auto rwSide = getSideRewritten(lit, orig);
//   return ord.compare(rwSide, EqHelper::getOtherEqualitySide(orig, rwSide)) == Ordering::GREATER;
// }

void InductionRewriting::output()
{
  CALL("InductionRewriting::output");
  auto s = iterTraits(_eqs.items()).collect<Stack>();
  std::sort(s.begin(),s.end(),[](pair<Clause*,unsigned> kv1, pair<Clause*,unsigned> kv2) {
    return kv1.second < kv2.second;
  });
  cout << (_downward ? "downward" : "upward") << " eqs" << endl;
  for (const auto& kv : s) {
    cout << *kv.first << " " << kv.second << endl;
  }
  cout << "end " << endl << endl;
}

ClauseIterator InductionRewriting::perform(
    Clause* rwClause, Literal* rwLit, TermList rwArg, TermList rwTerm,
    Clause* eqClause, Literal* eqLit, TermList eqLHS,
    ResultSubstitutionSP subst, bool eqIsResult)
{
  CALL("InductionRewriting::perform");
  // we want the rwClause and eqClause to be active
  ASS(rwClause->store()==Clause::ACTIVE);
  ASS(eqClause->store()==Clause::ACTIVE);

  // cout << "perform " << (_downward ? "downward" : "upward") << " rewriting with " << *rwClause << " and " << *eqClause << endl
  //   << "rwLit " << *rwLit << " eqLit " << *eqLit << endl
  //   << "rwArg " << rwArg << endl
  //   << "rwTerm " << rwTerm << " eqLHS " << eqLHS << endl
  //   // << "subst " << endl << subst->tryGetRobSubstitution()->toString() << endl
  //   << "eqIsResult " << eqIsResult << endl << endl;

  if (eqLHS.isVar()) {
    //The case where eqLHS is a variable suffices because superposition
    //is never carried out into variables. When unifying two terms
    //sort unification is guaranteed
    RobSubstitution* sub = subst->tryGetRobSubstitution();
    ASS(sub);
    TermList rwTermSort = SortHelper::getTermSort(rwTerm, rwLit);
    if(!sub->unify(SortHelper::getEqualityArgumentSort(eqLit), eqIsResult, rwTermSort, !eqIsResult)){
      //cannot perform superposition because sorts don't unify
      return ClauseIterator::getEmpty();
    }
  }

  if (rwArg.isVar() || rwTerm.isVar()) {
    return ClauseIterator::getEmpty();
  }

  TermList tgtTerm = EqHelper::getOtherEqualitySide(eqLit, eqLHS);
  TermList tgtTermS = subst->applyTo(tgtTerm, eqIsResult);
  TermList rwTermS = subst->applyTo(rwTerm, !eqIsResult);
  TermList rwArgS = subst->applyTo(rwArg, !eqIsResult);
  Literal* rwLitS = subst->applyTo(rwLit, !eqIsResult);
  if (!rwArgS.containsSubterm(rwTermS)) {
    return ClauseIterator::getEmpty();
  }

  if (!areEqualitySidesOriented(rwTermS, tgtTermS, _salg->getOrdering(), _downward)) {
    return ClauseIterator::getEmpty();
  }

  if (_salg->getOptions().lemmaGenerationHeuristics() && filterByHeuristics(rwClause, rwLit, rwTerm, eqClause, eqLit, eqLHS, subst)) {
    return ClauseIterator::getEmpty();
  }

  auto eqBound = _downward ? eqClause->getRewritingUpperBound() : eqClause->getRewritingLowerBound();
  if (eqBound) {
    auto eqBoundS = subst->applyTo(TermList(eqBound), eqIsResult).term();
    if (isTermViolatingBound(eqBoundS, rwTermS, _salg->getOrdering(), _downward)) {
      return ClauseIterator::getEmpty();
    }
  }

  auto bound = _downward ? rwClause->getRewritingUpperBound() : rwClause->getRewritingLowerBound();
  Term* boundS = nullptr;
  if (bound) {
    boundS = subst->applyTo(TermList(bound), !eqIsResult).term();
  }

  return pvi(iterTraits(vi(new SingleOccurrenceReplacementIterator(rwLitS, rwTermS.term(), tgtTermS)))
    .map([this,eqClause,rwClause,eqLit,rwLit,rwLitS,rwArgS,eqIsResult,subst,boundS](Literal* tgtLitS) -> Clause* {
      if (EqHelper::isEqTautology(tgtLitS)) {
        return nullptr;
      }
      auto newRwArg = getRewrittenTerm(rwLitS, tgtLitS);
      if (newRwArg != rwArgS) {
        return nullptr;
      }
      if (isTermViolatingBound(boundS, newRwArg, _salg->getOrdering(), _downward)) {
        return nullptr;
      }

      unsigned rwLength = rwClause->length();
      unsigned eqLength = eqClause->length();
      unsigned newLength = rwLength + (eqLength - 1);
      Inference inf(GeneratingInference2(
        _downward ? InferenceRule::INDUCTION_DOWNWARD_PARAMODULATION : InferenceRule::INDUCTION_UPWARD_PARAMODULATION,
        rwClause, eqClause));
      Clause* newCl = new(newLength) Clause(newLength, inf);

      (*newCl)[0] = tgtLitS;
      int next = 1;
      for(unsigned i=0;i<rwLength;i++) {
        Literal* curr=(*rwClause)[i];
        if(curr!=rwLit) {
          // cout << "rwClause " << *curr << endl;
          Literal *currAfter = subst->applyTo(curr,!eqIsResult);
          // cout << "rwClause after " << *currAfter << endl;
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
          // cout << "eqClause " << *curr << endl;
          Literal *currAfter = subst->applyTo(curr,eqIsResult);
          // cout << "eqClause after " << *currAfter << endl;

          if (EqHelper::isEqTautology(currAfter)) {
            newCl->destroy();
            return nullptr;
          }

          (*newCl)[next++] = currAfter;
        }
      }
      ASS_EQ(next, newLength);

      if (_downward) {
        if (eqIsResult) {
          env.statistics->forwardDownwardParamodulation++;
        } else {
          env.statistics->backwardDownwardParamodulation++;
        }
      } else {
        if (eqIsResult) {
          env.statistics->forwardUpwardParamodulation++;
        } else {
          env.statistics->backwardUpwardParamodulation++;
        }
      }
      auto ptr = _eqs.findPtr(eqClause);
      if (!ptr) {
        _eqs.insert(eqClause, 1);
      } else {
        (*ptr)++;
      }
      // cout << "result " << *newCl << endl << endl;
      ASS(newRwArg.isTerm());
      if (_salg->getOptions().symmetryBreakingParamodulation()) {
        newCl->setRewritingBound(newRwArg.term(), !_downward);
      }
      return newCl;
    }));
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

bool InductionRewriting::filterByHeuristics(
    Clause* rwClause, Literal* rwLit, TermList rwTerm,
    Clause* eqClause, Literal* eqLit, TermList eqLHS,
    ResultSubstitutionSP subst)
{
  if (eqLHS.isVar()) {
    return true;
  }
  vset<unsigned> eqSkolems = getSkolems(eqLit);
  if (!eqSkolems.empty()) {
    vset<unsigned> rwSkolems = getSkolems(rwLit);
    vset<unsigned> is;
    set_intersection(eqSkolems.begin(), eqSkolems.end(), rwSkolems.begin(), rwSkolems.end(), inserter(is, is.end()));
    if (is != eqSkolems) {
      return true;
    }
  }

  return false;
}

SimplifyingGeneratingInference::ClauseGenerationResult InductionSGIWrapper::generateSimplify(Clause* premise)
{
  CALL("InductionSGIWrapper::generateSimplify");
  // static unsigned cnt = 0;
  // cnt++;
  // if (cnt % 1000 == 0) {
  //   _dwRewriting->output();
  //   _uwRewriting->output();
  // }
  if (!premise->getRewritingLowerBound() && !premise->getRewritingUpperBound()) {
    return _generator->generateSimplify(premise);
  }
  ASS(!premise->getRewritingLowerBound() || !premise->getRewritingUpperBound());
  auto it = ClauseIterator::getEmpty();
  if (premise->getRewritingUpperBound()) {
    it = pvi(getConcatenatedIterator(it, _dwRewriting->generateClauses(premise)));
  }
  return ClauseGenerationResult {
    .clauses = pvi(iterTraits(it).concat(
      _induction->generateClauses(premise),
      _uwRewriting->generateClauses(premise))),
    .premiseRedundant = false,
  };
}

}
