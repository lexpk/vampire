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

namespace Inferences {

using namespace Lib;
using namespace Kernel;

bool isLiteralViolatingBound(Term* bound, Literal* lit, Ordering& ord)
{
  CALL("isLiteralViolatingBound");
  if (lit->isEquality()) {
    return true;
  }
  if (!bound || !bound->isLiteral()) {
    return false;
  }

  auto comp = ord.compare(static_cast<Literal*>(bound), lit);
  if (comp == Ordering::Result::EQUAL) {
    static unsigned cnt = 0;
    cnt++;
    if (cnt % 1000 == 0) {
      cout << "litequal " << cnt << endl;
    }
  }
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
    // filter out ones violating the bound
    .filter([bound,&ord,premise](Literal* lit) {
      return canUseLiteralForResolution(lit, premise) && !isLiteralViolatingBound(bound, lit, ord);
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

Clause* InductionResolution::perform(Clause* queryCl, Literal* queryLit, SLQueryResult qr)
{
  CALL("InductionResolution::generateClause");
  ASS(qr.clause->store()==Clause::ACTIVE);
  ASS(queryCl->store()==Clause::ACTIVE);
  ASS(!queryLit->isEquality());
  ASS(!qr.literal->isEquality());

  auto& opt = _salg->getOptions();
  if (!isGoalClause(opt, queryCl) && !isGoalClause(opt, qr.clause)) {
    return nullptr;
  }

  // check if inference is done by binary resolution
  if (queryCl->getLiteralPosition(queryLit) < queryCl->numSelected() &&
      qr.clause->getLiteralPosition(qr.literal) < qr.clause->numSelected())
  {
    return nullptr;
  }

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
    res->setRewritingBound(queryLitS->isPositive() ? queryLitS : resultLitS, false);
  }
  env.statistics->inductionResolution++;

  return res;
}

}
