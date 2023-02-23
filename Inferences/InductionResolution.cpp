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
 * @file InductionResolution.cpp
 * Implements class InductionResolution.
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

#define INDUCTION_MODE 1

namespace Inferences {

using namespace Lib;
using namespace Kernel;

bool isLiteralViolatingBound(Term* bound, Literal* lit, Ordering& ord)
{
  CALL("isLiteralViolatingBound");
  if (!bound || lit->isEquality()) {
    return false;
  }
  if (!bound->isLiteral()) {
    return true;
  }
  if (lit->isNegative()) {
    lit = Literal::complementaryLiteral(lit);
  }
  auto blit = static_cast<Literal*>(bound);
  ASS(blit->isPositive());

  auto comp = ord.compare(blit, lit);
  // cout << *bound << " " << *lit << " " << Ordering::resultToString(comp) << endl;
  return comp == Ordering::Result::LESS || comp == Ordering::Result::LESS_EQ;
}

bool canUseLiteralForResolution(Literal* lit, Clause* premise)
{
  CALL("InductionResolution::canUseLiteralForResolution");
  // cannot yet handle new variables that pop up
  if (iterTraits(premise->getVariableIterator())
      .any([&lit](unsigned v) {
        return !lit->containsSubterm(TermList(v, false));
      }))
  {
    return false;
  }
  return true;
}

VirtualIterator<Literal*> InductionResolution::getIterator(Ordering& ord, Clause* premise)
{
  CALL("InductionResolution::getIterator");
  Term* bound = premise->getRewritingUpperBound();
  return pvi(iterTraits(premise->iterLits())
    .filter([](Literal* lit) {
      return !lit->isEquality();
    })
    // filter out ones violating the bound
    .filter([bound,&ord,premise](Literal* lit) {
      return !isLiteralViolatingBound(bound, lit, ord)
#if INDUCTION_MODE
        && canUseLiteralForResolution(lit, premise)
#endif
      ;
    }));
}

bool isGoalClause(const Options& opt, Clause* premise)
{
  CALL("InductionResolution::isGoalClause");
  if ((!opt.nonUnitInduction() || opt.splitting()) &&
    (!InductionHelper::isInductionClause(premise) || !InductionHelper::isInductionLiteral((*premise)[0])))
  {
    return false;
  }
  return true;
}

// inference

void InductionResolution::attach(SaturationAlgorithm* salg)
{
  CALL("InductionResolution::attach");
  GeneratingInferenceEngine::attach(salg);
  _index=static_cast<LiteralIndex*>(
	  _salg->getIndexManager()->request(INDUCTION_LITERAL_INDEX) );
}

void InductionResolution::detach()
{
  CALL("InductionResolution::detach");
  _index = 0;
  _salg->getIndexManager()->release(INDUCTION_LITERAL_INDEX);
  GeneratingInferenceEngine::detach();
}

ClauseIterator InductionResolution::generateClauses(Clause* premise)
{
  CALL("InductionResolution::generateClauses");
  if (premise->getRewritingLowerBound()) {
    return ClauseIterator::getEmpty();
  }

  return pvi(iterTraits(getIterator(_salg->getOrdering(), premise))
    .flatMap([this](Literal* lit) {
      return pvi( pushPairIntoRightIterator(lit, _index->getUnifications(lit, true)) );
    })
    .map([this, premise](pair<Literal*, SLQueryResult> arg) {
      return perform(premise, arg.first, arg.second);
    })
    .filter(NonzeroFn())
    .timeTraced("induction resolution"));
}

inline bool termAlgebraFunctor(unsigned functor) {
  auto sym = env.signature->getFunction(functor);
  return sym->termAlgebraCons() || sym->termAlgebraDest();
}

bool hasTermToInductOn(Literal* lit)
{
  static const bool intInd = InductionHelper::isIntInductionOn();
  static const bool structInd = InductionHelper::isStructInductionOn();
  NonVariableNonTypeIterator stit(lit, false);
  while (stit.hasNext()) {
    auto st = stit.next();
    if (InductionHelper::isInductionTermFunctor(st.term()->functor()) &&
      ((structInd && !termAlgebraFunctor(st.term()->functor()) && InductionHelper::isStructInductionTerm(st.term())) ||
       (intInd && InductionHelper::isIntInductionTermListInLiteral(st, lit))))
    {
      return true;
    }
  }
}

bool filterByHeuristics(Clause* queryCl, Literal* queryLit, Clause* resultCl, Literal* resultLit, const Options& opt)
{
  // if (eqClause->isPureTheoryDescendant() || rwClause->isPureTheoryDescendant()) {
  //   return true;
  // }

  if (opt.nonUnitInduction() && !opt.splitting()) {
    return false;
  }
  bool found = false;
  for (unsigned i = 0; i < queryCl->length(); i++) {
    auto lit = (*queryCl)[i];
    if (lit != queryLit && hasTermToInductOn(lit)) {
      found = true;
      break;
    }
  }
  if (!found) {
    return true;
  }
  found = false;
  for (unsigned i = 0; i < resultCl->length(); i++) {
    auto lit = (*resultCl)[i];
    if (lit != resultLit && hasTermToInductOn(lit)) {
      found = true;
      break;
    }
  }
  // if (!_downward && eqClause->length() == 1 && rhs.isTerm() && !hasTermToInductOn(rhs.term(), eqLit)) {
  //   return true;
  // }

  return !found;
}

Clause* InductionResolution::perform(Clause* queryCl, Literal* queryLit, SLQueryResult qr)
{
  CALL("InductionResolution::generateClause");
  ASS(qr.clause->store()==Clause::ACTIVE);
  ASS(queryCl->store()==Clause::ACTIVE);
  ASS(!queryLit->isEquality());
  ASS(!qr.literal->isEquality());
  ASS(!queryCl->getRewritingLowerBound());
  ASS(!qr.clause->getRewritingLowerBound());
  // cout << "RES " << *queryLit << " " << *qr.literal << endl
  //      << "    " << *qr.clause << endl;

  auto& opt = _salg->getOptions();
#if INDUCTION_MODE
  if (!isGoalClause(opt, queryCl) && !isGoalClause(opt, qr.clause)) {
    return nullptr;
  }
  if (filterByHeuristics(queryCl, queryLit, qr.clause, qr.literal, opt)) {
    return nullptr;
  }
#endif

  auto queryLitS = qr.substitution->applyToQuery(queryLit);
  auto queryBound = queryCl->getRewritingUpperBound();
  ASS(!queryCl->getRewritingLowerBound());
  if (queryBound && queryBound->isLiteral()) {
    auto queryBoundS = qr.substitution->applyToQuery(static_cast<Literal*>(queryBound));
    if (isLiteralViolatingBound(queryBoundS, queryLitS, _salg->getOrdering())) {
      return nullptr;
    }
  }

  auto resultLitS = qr.substitution->applyToResult(qr.literal);
  auto resultBound = qr.clause->getRewritingUpperBound();
  ASS(!qr.clause->getRewritingLowerBound());
  if (resultBound && resultBound->isLiteral()) {
    auto resultBoundS = qr.substitution->applyToResult(static_cast<Literal*>(resultBound));
    if (isLiteralViolatingBound(resultBoundS, resultLitS, _salg->getOrdering())) {
      return nullptr;
    }
  }
  Inference inf(GeneratingInference2(InferenceRule::INDUCTION_RESOLUTION, queryCl, qr.clause));

  unsigned clength = queryCl->length();
  unsigned dlength = qr.clause->length();
  unsigned newLength = clength+dlength-2;

  Clause* res = new(newLength) Clause(newLength, inf);

  unsigned next = 0;
  for(unsigned i=0;i<clength;i++) {
    Literal* curr=(*queryCl)[i];
    if(curr!=queryLit) {
      ASS(next < newLength);
      (*res)[next] = qr.substitution->applyToQuery(curr);
      next++;
    }
  }

  for(unsigned i=0;i<dlength;i++) {
    Literal* curr=(*qr.clause)[i];
    if(curr!=qr.literal) {
      (*res)[next] = qr.substitution->applyToResult(curr);
      next++;
    }
  }

  // cout << "RESOLUTION BETWEEN " << *queryCl << endl
  //      << "AND " << *qr.clause << endl
  //      << "RESULT " << *res << endl;
  if (opt.symmetryBreakingParamodulation()) {
    res->setRewritingBound(queryLitS, false);
  }
  bool boundEqual = false;
  if (queryBound && queryBound->isLiteral()) {
    auto queryBoundS = qr.substitution->applyToQuery(static_cast<Literal*>(queryBound));
    if (queryBoundS == queryLitS) {
      boundEqual = true;
    }
  }
  if (!boundEqual && resultBound && resultBound->isLiteral()) {
    auto resultBoundS = qr.substitution->applyToResult(static_cast<Literal*>(resultBound));
    if (resultBoundS == resultLitS) {
      boundEqual = true;
    }
  }
  if (boundEqual) {
    env.statistics->symParBoundEqualResolution++;
  }

  env.statistics->inductionResolution++;

  return res;
}

}
