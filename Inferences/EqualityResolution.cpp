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
 * @file EqualityResolution.cpp
 * Implements class EqualityResolution.
 */

#include <utility>

#include "Lib/VirtualIterator.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/PairUtils.hpp"
#include "Lib/Stack.hpp"

#include "Lib/Environment.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/Options.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Unit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/LiteralSelector.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/ApplicativeHelper.hpp"

#include "Saturation/SaturationAlgorithm.hpp"


#include "EqualityResolution.hpp"

#if VDEBUG
#include <iostream>
using namespace std;
#endif

namespace Inferences
{

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

struct EqualityResolution::IsNegativeEqualityFn
{
  bool operator()(Literal* l)
  { return l->isEquality() && l->isNegative(); }
};

struct EqualityResolution::ResultFn
{
  ResultFn(Clause* cl, bool afterCheck = false, Ordering* ord = nullptr)
      : _afterCheck(afterCheck), _ord(ord), _cl(cl), _cLen(cl->length()) {}

  Clause* operator() (Literal* lit)
  {
    CALL("EqualityResolution::ResultFn::operator()");

    ASS(lit->isEquality());
    ASS(lit->isNegative());

    static unique_ptr<MismatchHandler> _mismatchHandler = MismatchHandler::create();
    auto handler = _mismatchHandler.get();

    TermList arg0 = *lit->nthArgument(0);
    TermList arg1 = *lit->nthArgument(1);

    // We only care about non-trivial constraints where the top-sybmol of the two literals are the same
    // and therefore a constraint can be created between arguments
    if(handler &&  arg0.isTerm() && arg1.isTerm() &&
       arg0.term()->functor() != arg1.term()->functor()){
      handler = nullptr;
    }

    AbstractingUnifier absUnif(handler);

    if(!absUnif.unify(arg0,0,arg1,0)){ 
      return 0; 
    }

    for (auto &c : absUnif.constr().iter()) {
      if (!handler->recheck(c.lhs(absUnif.subs()), c.rhs(absUnif.subs())))
        return nullptr;
    }
    // TODO create absUnif.constrLiterals or so
    auto constraints = absUnif.constr().literals(absUnif.subs());
    unsigned newLen=_cLen - 1 + constraints->length();

    Clause* res = new(newLen) Clause(newLen, GeneratingInference1(InferenceRule::EQUALITY_RESOLUTION, _cl));

    Literal* litAfter = 0;

    if (_afterCheck && _cl->numSelected() > 1) {
      TIME_TRACE(TimeTrace::LITERAL_ORDER_AFTERCHECK);
      litAfter = absUnif.subs().apply(lit, 0);
    }

    unsigned next = 0;
    for(unsigned i=0;i<_cLen;i++) {
      Literal* curr=(*_cl)[i];
      if(curr!=lit) {
        Literal* currAfter = absUnif.subs().apply(curr, 0);

        if (litAfter) {
          TIME_TRACE(TimeTrace::LITERAL_ORDER_AFTERCHECK);

          if (i < _cl->numSelected() && _ord->compare(currAfter,litAfter) == Ordering::GREATER) {
            env.statistics->inferencesBlockedForOrderingAftercheck++;
            res->destroy();
            return 0;
          }
        }

        (*res)[next++] = currAfter;
      }
    }
    for (auto l : *constraints) {
      (*res)[next++] = l;
    }
    ASS_EQ(next,newLen);

    env.statistics->equalityResolution++;

    return res;
  }
private:
  bool _afterCheck;
  Ordering* _ord;
  Clause* _cl;
  unsigned _cLen;
};

ClauseIterator EqualityResolution::generateClauses(Clause* premise)
{
  CALL("EqualityResolution::generateClauses");

  if(premise->isEmpty()) {
    return ClauseIterator::getEmpty();
  }
  ASS(premise->numSelected()>0);

  auto it1 = premise->getSelectedLiteralIterator();

  auto it2 = getFilteredIterator(it1,IsNegativeEqualityFn());

  auto it3 = getMappingIterator(it2,ResultFn(premise,
      getOptions().literalMaximalityAftercheck() && _salg->getLiteralSelector().isBGComplete(),
      &_salg->getOrdering()));

  auto it4 = getFilteredIterator(it3,NonzeroFn());

  return pvi( it4 );
}

/**
 * @c toResolve must be an negative equality. If it is resolvable,
 * resolve it and return the resulting clause. If it is not resolvable,
 * return 0.
 */
Clause* EqualityResolution::tryResolveEquality(Clause* cl, Literal* toResolve)
{
  CALL("EqualityResolution::tryResolveEquality");

  return ResultFn(cl)(toResolve);
}

}
