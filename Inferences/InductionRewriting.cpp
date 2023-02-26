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

#define INDUCTION_MODE 1

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

bool comparisonViolates(Ordering::Result comp, bool downward)
{
  if (downward) {
    return comp == Ordering::Result::LESS || comp == Ordering::Result::LESS_EQ;
  }
  return comp == Ordering::Result::GREATER || comp == Ordering::Result::GREATER_EQ;
}

bool isTermListViolatingBound(Term* bound, TermList t, Ordering& ord, bool downward)
{
  CALL("isTermListViolatingBound");
  if (!bound) {
    return false;
  }
  // predicates are always greater than non-predicates
  if (t.isVar()) {
    if (bound->isLiteral()) {
      return false;
    }
    return comparisonViolates(ord.compare(TermList(bound), t), downward);
  }
  return InductionRewriting::isTermViolatingBound(bound, t.term(), ord, downward);
}

bool InductionRewriting::isTermViolatingBound(Term* bound, Term* t, Ordering& ord, bool downward)
{
  CALL("InductionRewriting::isTermViolatingBound");
  if (!bound) {
    return false;
  }
  // predicates are always greater than non-predicates
  if (bound->isLiteral() && !t->isLiteral()) {
    return false;
  }
  if (!bound->isLiteral() && t->isLiteral()) {
    return true;
  }
  ASS_EQ(bound->isLiteral(), t->isLiteral());
  Ordering::Result comp;
  if (bound->isLiteral()) {
    auto blit = static_cast<Literal*>(bound);
    auto tlit = static_cast<Literal*>(t);

    ASS(blit->isPositive());
    if (tlit->isNegative()) {
      tlit = Literal::complementaryLiteral(tlit);
    }
    comp = ord.compare(blit,tlit);
  } else {
    comp = ord.compare(TermList(bound), TermList(t));
  }
  return comparisonViolates(comp, downward);
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
      return !isTermListViolatingBound(bound, kv.second, ord, downward);
    }));
}

bool isClauseRewritable(const Options& opt, Clause* premise, bool downward)
{
  CALL("InductionRewriting::isClauseRewritable");
  if (!downward && (!opt.nonUnitInduction() || opt.splitting()) &&
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

inline bool termAlgebraFunctor(unsigned functor) {
  auto sym = env.signature->getFunction(functor);
  return sym->termAlgebraCons() || sym->termAlgebraDest();
}

inline bool hasTermToInductOn(Term* t, Literal* l) {
  static const bool intInd = InductionHelper::isIntInductionOn();
  static const bool structInd = InductionHelper::isStructInductionOn();
  NonVariableNonTypeIterator stit(t);
  while (stit.hasNext()) {
    auto st = stit.next();
    if (InductionHelper::isInductionTermFunctor(st.term()->functor()) &&
      ((structInd && !termAlgebraFunctor(st.term()->functor()) && InductionHelper::isStructInductionTerm(st.term())) ||
       (intInd && InductionHelper::isIntInductionTermListInLiteral(st, l))))
    {
      return true;
    }
  }
  return false;
}

bool canUseLHSForRewrite(LitArgPair kv, Clause* premise, const Options& opt, bool downward)
{
  CALL("InductionRewriting::canUseLHSForRewrite");
  auto lit = kv.first;
  auto lhs = kv.second;
  // cannot yet handle new variables that pop up
  if (iterTraits(premise->getVariableIterator())
      .any([&lhs](unsigned v) {
        return !lhs.containsSubterm(TermList(v, false));
      }))
  {
    return false;
  }

  if (opt.lemmaGenerationHeuristics()) {
    // lhs contains only things we cannot induct on
    auto rhs = EqHelper::getOtherEqualitySide(lit, TermList(lhs));
    // if ((!opt.nonUnitInduction() || opt.splitting()) && (rhs.isVar() || !hasTermToInductOn(rhs.term(), eqLit))) {
    //   return true;
    // }
    if (!downward && premise->length() == 1 && rhs.isTerm() && !hasTermToInductOn(rhs.term(), lit)) {
      return true;
    }
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
#if INDUCTION_MODE
  if (!isClauseRewritable(opt, premise, downward)) {
    return LitArgPairIter::getEmpty();
  }
#endif
  return pvi(iterTraits(getIterator(ord, premise, downward)));
}

LitArgPairIter InductionRewriting::getLHSIterator(Clause* premise, const Options& opt, Ordering& ord, bool downward)
{
  CALL("InductionRewriting::getLHSIterator");
#if INDUCTION_MODE
  auto lemmaGen = k_theoryAxiomsForLemmaGeneration && premise->isPureTheoryDescendant();
#endif
  return pvi(iterTraits(getIterator(ord, premise, downward))
#if INDUCTION_MODE
    .filter([&opt,lemmaGen](LitArgPair kv) {
      return opt.inductionEquationalLemmaGeneration()==Options::LemmaGeneration::ALL || kv.first->isForLemmaGeneration() || lemmaGen;
    })
#endif
    .filter([&ord, downward](LitArgPair kv) {
      auto lit = kv.first;
      if (!lit->isEquality() || lit->isNegative()) {
        return false;
      }
      auto lhs = kv.second;
      return areEqualitySidesOriented(lhs, EqHelper::getOtherEqualitySide(lit, lhs), ord, downward);
    })
#if INDUCTION_MODE
    .filter([premise,&opt,downward](LitArgPair kv) {
      return canUseLHSForRewrite(kv, premise, opt, downward);
    }));
#else
    );
#endif
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
  if (_downward && premise->getRewritingLowerBound()) {
    return ClauseIterator::getEmpty();
  }

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
  if (oldLit->isEquality()) {
    auto lhsNew = *newLit->nthArgument(0);
    auto rhsNew = *newLit->nthArgument(1);
    auto lhsOld = *oldLit->nthArgument(0);
    auto rhsOld = *oldLit->nthArgument(1);
    if (lhsNew == lhsOld || rhsNew == lhsOld) {
      return rhsOld;
    }
    ASS(lhsNew == rhsOld || rhsNew == rhsOld);
    return lhsOld;
  }
  return TermList(oldLit);
}

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
  ASS(!_downward || !(rwClause->getRewritingLowerBound() && eqClause->getRewritingLowerBound()));

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

#if INDUCTION_MODE
  if (_salg->getOptions().lemmaGenerationHeuristics() && filterByHeuristics(rwClause, rwLit, rwTerm, eqClause, eqLit, eqLHS, subst, _salg->getOptions())) {
    return ClauseIterator::getEmpty();
  }
#endif

  TermList rwTermS = subst->applyTo(rwTerm, !eqIsResult);
  TermList rwArgS;
  if (rwArg.term()->isLiteral()) {
    rwArgS = TermList(subst->applyTo(static_cast<Literal*>(rwArg.term()), !eqIsResult));
  } else {
    rwArgS = subst->applyTo(rwArg, !eqIsResult);
  }
  if (!rwArgS.containsSubterm(rwTermS)) {
    return ClauseIterator::getEmpty();
  }

  TermList tgtTerm = EqHelper::getOtherEqualitySide(eqLit, eqLHS);
  TermList tgtTermS = subst->applyTo(tgtTerm, eqIsResult);
  ASS(rwArg.isTerm());
  Literal* rwLitS = subst->applyTo(rwLit, !eqIsResult);

  if (!areEqualitySidesOriented(rwTermS, tgtTermS, _salg->getOrdering(), _downward)) {
    return ClauseIterator::getEmpty();
  }

  auto eqBound = _downward ? eqClause->getRewritingUpperBound() : eqClause->getRewritingLowerBound();
  auto compTerm = _downward ? rwTermS : rwArgS;
  Term* eqBoundS = nullptr;
  if (eqBound) {
    if (eqBound->isLiteral()) {
      eqBoundS = subst->applyTo(static_cast<Literal*>(eqBound), eqIsResult);
    } else {
      eqBoundS = subst->applyTo(TermList(eqBound), eqIsResult).term();
    }
    if (isTermListViolatingBound(eqBoundS, compTerm, _salg->getOrdering(), _downward)) {
      return ClauseIterator::getEmpty();
    }
  }

  auto bound = _downward ? rwClause->getRewritingUpperBound() : rwClause->getRewritingLowerBound();
  Term* boundS = nullptr;
  if (bound) {
    if (bound->isLiteral()) {
      boundS = subst->applyTo(static_cast<Literal*>(bound), !eqIsResult);
    } else {
      boundS = subst->applyTo(TermList(bound), !eqIsResult).term();
    }
  }

  return pvi(iterTraits(vi(new SingleOccurrenceReplacementIterator(rwLitS, rwTermS.term(), tgtTermS)))
    .map([this,eqClause,rwClause,eqLit,rwLit,rwLitS,rwArgS,eqIsResult,subst,boundS,eqBoundS,compTerm](Literal* tgtLitS) -> Clause* {
      if (EqHelper::isEqTautology(tgtLitS)) {
        return nullptr;
      }
      auto newRwArg = getRewrittenTerm(rwLitS, tgtLitS);
      if (newRwArg != rwArgS) {
        return nullptr;
      }
      if (isTermListViolatingBound(boundS, newRwArg, _salg->getOrdering(), _downward)) {
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
      // auto ptr = _eqs.findPtr(eqClause);
      // if (!ptr) {
      //   _eqs.insert(eqClause, 1);
      // } else {
      //   (*ptr)++;
      // }
      // cout << "result " << *newCl << endl << endl;
      ASS(newRwArg.isTerm());
      if (_salg->getOptions().symmetryBreakingParamodulation()) {
        newCl->setRewritingBound(newRwArg.term(), !_downward);
      }
      bool boundEqual = false;
      if (newRwArg.term() == boundS) {
        ASS_EQ(newRwArg.term()->isLiteral(),boundS->isLiteral());
        boundEqual = true;
      }
      ASS(compTerm.isTerm());
      if (!boundEqual && eqBoundS && compTerm.term() == eqBoundS) {
        ASS_EQ(eqBoundS->isLiteral(),compTerm.term()->isLiteral());
        boundEqual = true;
      }
      if (boundEqual) {
        env.statistics->symParBoundEqual++;
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
    ResultSubstitutionSP subst, const Options& opt)
{
  // if (eqClause->isPureTheoryDescendant() || rwClause->isPureTheoryDescendant()) {
  //   return true;
  // }
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
