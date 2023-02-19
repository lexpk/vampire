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

#include "InductionResolution.hpp"
#include "InductionRewriting.hpp"

namespace Inferences {

using namespace Lib;
using namespace Kernel;

static bool k_theoryAxiomsForLemmaGeneration = false;

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
  ASS(t.isTerm());
  if (!bound) {
    return false;
  }
  if (bound->isLiteral() && !t.term()->isLiteral()) {
    return true;
  }
  if (!bound->isLiteral() && t.term()->isLiteral()) {
    return false;
  }
  ASS_EQ(bound->isLiteral(),t.term()->isLiteral());
  Ordering::Result comp;
  if (bound->isLiteral()) {
    comp = ord.compare(static_cast<Literal*>(bound),static_cast<Literal*>(t.term()));
  } else {
    comp = ord.compare(TermList(bound), TermList(t));
  }
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
      if (lit->isEquality()) {
        return pvi(pushPairIntoRightIterator(lit, termArgIter(lit)));
      }
      return pvi(pushPairIntoRightIterator(lit, getSingletonIterator(TermList(lit))));
    })
    // filter out ones violating the bound
    .filter([bound,&ord,downward](LitArgPair kv) {
      return kv.second.isTerm() && !isTermViolatingBound(bound, kv.second, ord, downward);
    }));
}

bool isClauseRewritable(const Options& opt, Clause* premise)
{
  CALL("InductionRewriting::isClauseRewritable");
  if ((!opt.nonUnitInduction() || opt.splitting()) &&
    (!InductionHelper::isInductionClause(premise) || !InductionHelper::isInductionLiteral((*premise)[0])))
  {
    return false;
  }
  return true;
}

bool areEqualitySidesOriented(TermList lhs, TermList rhs, Ordering& ord, bool downward)
{
  CALL("InductionRewriting::areTermsOriented");
  ASS(lhs.isVar() || !lhs.term()->isLiteral());
  ASS(rhs.isVar() || !rhs.term()->isLiteral());

  auto comp = ord.compare(rhs,lhs);
  if (downward && Ordering::isGorGEorE(comp)) {
    return false;
  }
  if (!downward && !Ordering::isGorGEorE(comp)) {
    return false;
  }
  return true;
}

bool canUseLHSForRewrite(LitArgPair kv, Clause* premise)
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
  return true;
}

void InductionRewriting::markTheoryAxiomsForLemmaGeneration()
{
  k_theoryAxiomsForLemmaGeneration = true;
}

LitArgPairIter InductionRewriting::getTermIterator(Clause* premise, const Options& opt, Ordering& ord, bool downward)
{
  CALL("InductionRewriting::getTermIterator");
  if (!isClauseRewritable(opt, premise)) {
    return LitArgPairIter::getEmpty();
  }
  return pvi(iterTraits(getIterator(ord, premise, downward)));
}

LitArgPairIter InductionRewriting::getLHSIterator(Clause* premise, const Options& opt, Ordering& ord, bool downward)
{
  CALL("InductionRewriting::getLHSIterator");
  auto lemmaGen = k_theoryAxiomsForLemmaGeneration && premise->isTheoryAxiom();
  return pvi(iterTraits(getIterator(ord, premise, downward))
    .filter([&opt,lemmaGen](LitArgPair kv) {
      return opt.inductionEquationalLemmaGeneration()==Options::LemmaGeneration::ALL || kv.first->isForLemmaGeneration() || lemmaGen;
    })
    .filter([&ord, downward](LitArgPair kv) {
      auto lit = kv.first;
      if (!lit->isEquality() || lit->isNegative()) {
        return false;
      }
      auto lhs = kv.second;
      return areEqualitySidesOriented(lhs, EqHelper::getOtherEqualitySide(lit, lhs), ord, downward);
    })
    .filter([premise](LitArgPair kv) {
      return canUseLHSForRewrite(kv, premise);
    }));
}

// inference

void InductionRewriting::attach(SaturationAlgorithm* salg)
{
  CALL("InductionRewriting::attach");
  GeneratingInferenceEngine::attach(salg);
  _lhsIndex=static_cast<TermIndex*>(
	  _salg->getIndexManager()->request(_downward ? DOWNWARD_REWRITING_LHS_INDEX : UPWARD_REWRITING_LHS_INDEX) );
  _termIndex=static_cast<TermIndex*>(
	  _salg->getIndexManager()->request(_downward ? DOWNWARD_REWRITING_SUBTERM_INDEX : UPWARD_REWRITING_SUBTERM_INDEX) );
}

void InductionRewriting::detach()
{
  CALL("InductionRewriting::detach");
  _termIndex = 0;
  _salg->getIndexManager()->release(_downward ? DOWNWARD_REWRITING_SUBTERM_INDEX : UPWARD_REWRITING_SUBTERM_INDEX);
  _lhsIndex = 0;
  _salg->getIndexManager()->release(_downward ? DOWNWARD_REWRITING_LHS_INDEX : UPWARD_REWRITING_LHS_INDEX);
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
      NonVariableNonTypeIterator it(kv.second.term(), !kv.second.term()->isLiteral());
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
      if (arg.second.literal->isEquality()) {
        return pvi(pushPairIntoRightIterator(arg, termArgIter(arg.second.literal)));
      }
      return pvi(pushPairIntoRightIterator(arg, getSingletonIterator(TermList(arg.second.literal))));
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
    return TermList(oldLit);
    // for (unsigned i = 0; i < oldLit->arity(); i++) {
    //   auto oldArg = *oldLit->nthArgument(i);
    //   auto newArg = *newLit->nthArgument(i);
    //   if (oldArg != newArg) {
    //     return oldArg;
    //   }
    // }
    // ASSERTION_VIOLATION;
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

}
