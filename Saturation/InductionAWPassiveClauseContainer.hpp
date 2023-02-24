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
 * @file InductionAWPassiveClauseContainer.hpp
 * Defines the class InductionAWPassiveClauseContainer
 * @since 31/12/2007 Manchester
 */

#ifndef __InductionAWPassiveClauseContainer__
#define __InductionAWPassiveClauseContainer__

#include "AWPassiveClauseContainer.hpp"
#include "Lib/STL.hpp"

namespace Saturation {

using namespace Kernel;

class InductionQueue
: public ClauseQueue
{
public:
  InductionQueue(const Options& opt) : _opt(opt), _restrictions(nullptr) {}
  bool lessThan(Clause* c1, Clause* c2) override;
  float calculateValue(Clause* cl);
  void setRestrictions(void* r) {
    _restrictions = r;
  }

private:
  vmap<Clause*,float> _m;
  const Options& _opt;
  void* _restrictions;
};

class InductionAWPassiveClauseContainer
: public AWPassiveClauseContainer
{
public:
  CLASS_NAME(InductionAWPassiveClauseContainer);
  USE_ALLOCATOR(InductionAWPassiveClauseContainer);

  InductionAWPassiveClauseContainer(bool isOutermost, const Shell::Options& opt, vstring name);

  void add(Clause* cl) override;
  void remove(Clause* cl) override;

  Clause* popSelected() override;
  bool isEmpty() const override
  { return _inductionQueue.isEmpty() && AWPassiveClauseContainer::isEmpty(); }

  void setInductionRestrictions(void* r) override {
    _inductionQueue.setRestrictions(r);
  }

private:
  InductionQueue _inductionQueue;
  bool _isOutermost;
}; // class InductionAWPassiveClauseContainer

};

#endif /* __InductionAWPassiveClauseContainer__ */