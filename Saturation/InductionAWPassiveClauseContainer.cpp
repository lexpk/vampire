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
 * @file InductionAWPassiveClauseContainer.cpp
 * Implements class InductionAWPassiveClauseContainer for the queue of passive clauses.
 */

#include "Kernel/Clause.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"

#include "Lib/Set.hpp"

#include "Inferences/Induction.hpp"

#include "InductionAWPassiveClauseContainer.hpp"

#define NON_INDUCTION_CLAUSE_COEFF 10.0f
#define NON_INDUCTION_LITERAL_COEFF 10.0f

namespace Saturation
{
using namespace Lib;
using namespace Kernel;
using namespace Inferences;

float InductionQueue::calculateValue(Clause* cl)
{
  CALL("InductionQueue::calculateValue");
  ASS(_restrictions);
  auto it = _m.find(cl);
  if (it == _m.end()) {
    float w = 0.0f;
    auto indcl = InductionHelper::isInductionClause(cl);
    unsigned nonindlits = cl->length();
    for (unsigned i = 0; i < cl->length(); i++) {
      auto lit = (*cl)[i];
      if (indcl && InductionHelper::isInductionLiteral(lit)) {
        nonindlits--;
      }
      w += lit->iweight(_restrictions);
    }
    if (!indcl) {
      w *= NON_INDUCTION_CLAUSE_COEFF;
    }
    if (nonindlits) {
      w *= NON_INDUCTION_LITERAL_COEFF * nonindlits;
    }
    it = _m.insert(make_pair(cl,w)).first;
    // cout << "val " << it->second << " " << *cl << endl;
  }
  return it->second;
}

bool InductionQueue::lessThan(Clause* c1,Clause* c2)
{
  CALL("InductionQueue::lessThan");
  unsigned n1 = calculateValue(c1);
  unsigned n2 = calculateValue(c2);
  if (n1 != n2) {
    return n1 < n2;
  }
  Comparison weightCmp=AWPassiveClauseContainer::compareWeight(c1, c2, _opt);
  if (weightCmp!=EQUAL) {
    return weightCmp==LESS;
  }
  return c1->number() < c2->number();
}

InductionAWPassiveClauseContainer::InductionAWPassiveClauseContainer(bool isOutermost, const Shell::Options& opt, vstring name)
: AWPassiveClauseContainer(false, opt, name), _inductionQueue(opt), _isOutermost(isOutermost) {}

void InductionAWPassiveClauseContainer::add(Clause* cl)
{
  CALL("InductionAWPassiveClauseContainer::add");
  AWPassiveClauseContainer::add(cl);
  _inductionQueue.insert(cl);

  if (_isOutermost)
  {
    addedEvent.fire(cl);
  }
}

void InductionAWPassiveClauseContainer::remove(Clause* cl)
{
  CALL("InductionAWPassiveClauseContainer::remove");
  if (_isOutermost)
  {
    ASS(cl->store()==Clause::PASSIVE);
  }
  _inductionQueue.remove(cl);
  AWPassiveClauseContainer::remove(cl);
  if (_isOutermost)
  {
    removedEvent.fire(cl);
    ASS(cl->store()!=Clause::PASSIVE);
  }
}

Clause* InductionAWPassiveClauseContainer::popSelected()
{
  CALL("InductionAWPassiveClauseContainer::popSelected");
  ASS( ! isEmpty());

  static unsigned count = 0;
  count++;

  Clause* cl;
  if(count % 2 == 0) {
    cl = AWPassiveClauseContainer::popSelected();
    _inductionQueue.remove(cl);
  } else {
    cl = _inductionQueue.pop();
    auto val = _inductionQueue.calculateValue(cl);
    // cout << "popped value " << val << " " << *cl << endl;
    AWPassiveClauseContainer::remove(cl);
  }

  if (_isOutermost) {
    selectedEvent.fire(cl);
  }

  return cl;
}

}
