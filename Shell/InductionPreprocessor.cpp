
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
 * @file InductionPreprocessor.cpp
 * Implements class InductionPreprocessor.
 */

#include "Kernel/TermIterators.hpp"

#include "InductionPreprocessor.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Problem.hpp"

namespace Shell
{

using namespace Kernel;
using namespace Lib; 

bool isFunctionHeader(TermList ts) {
  if (ts.isVar()) {
    return false;
  }
  auto t = ts.term();
  auto sym = env.signature->getFunction(t->functor());
  if (sym->termAlgebraCons() || sym->termAlgebraDest() || sym->interpreted() || sym->introduced()) {
    return false;
  }
  NonVariableNonTypeIterator nvi(t);
  if (!nvi.hasNext()) {
    // require at least one non-variable
    return false;
  }
  while (nvi.hasNext()) {
    auto st = nvi.next();
    auto sts = env.signature->getFunction(st.term()->functor());
    if (!sts->termAlgebraCons() && !sts->termAlgebraDest()) {
      return false;
    }
  }
  return true;
}

void InductionPreprocessor::preprocess(const Problem& prb)
{
  UnitList::Iterator uit(prb.units());
  while(uit.hasNext()) {
    auto unit = uit.next();
    Clause* cl=static_cast<Clause*>(unit);
    ASS(cl->isClause());
    for (unsigned i = 0; i < cl->length(); i++) {
      auto lit = (*cl)[i];
      if (!lit->isEquality() || lit->isNegative()) {
        continue;
      }
      for (unsigned j = 0; j <= 1; j++) {
        auto side = *lit->nthArgument(j);
        if (side.isVar()) {
          continue;
        }
        auto fn = side.term()->functor();
        auto other = *lit->nthArgument(1-j);
        if (!isFunctionHeader(side) || other.isVar()) {
          continue;
        }
        NonVariableNonTypeIterator nvi(other.term(), true);
        while (nvi.hasNext()) {
          auto st = nvi.next();
          if (st.term()->functor() != fn) {
            continue;
          }
          unsigned cnt = 0;
          for (unsigned k = 0; k < side.term()->arity(); k++) {
            if (*side.term()->nthArgument(k) != *st.term()->nthArgument(k)) {
              cnt++;
            }
          }
          if (cnt > 1) {
            auto symb = env.signature->getFunction(fn);
            symb->markSuggestsMultiTermInduction();
          }
        }
      }
    }
  }
}

}