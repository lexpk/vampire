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
 * @file AWPassiveClauseContainer.hpp
 * Defines the class AWPassiveClauseContainer
 * @since 31/12/2007 Manchester
 */

#ifndef __AWPassiveClauseContainer__
#define __AWPassiveClauseContainer__

#include <memory>
#include <vector>
#include "Lib/Comparison.hpp"
#include "Lib/DHMap.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/ClauseQueue.hpp"
#include "ClauseContainer.hpp"

#include "Lib/Allocator.hpp"

#include "Lib/Random.hpp"
#include <torch/script.h>

namespace Saturation {

using namespace Kernel;

class AgeQueue
: public ClauseQueue
{
public:
  AgeQueue(const Options& opt) : _opt(opt) {}
protected:

  virtual bool lessThan(Clause*,Clause*);

  friend class AWPassiveClauseContainer;

private:
  const Shell::Options& _opt;
};

class WeightQueue
  : public ClauseQueue
{
public:
  WeightQueue(const Options& opt) : _opt(opt) {}
protected:
  virtual bool lessThan(Clause*,Clause*);

  friend class AWPassiveClauseContainer;
private:
  const Shell::Options& _opt;
};

class ScoreQueue
  : public ClauseQueue
{
public:
  ScoreQueue(const DHMap<Clause*,double>& scores) : _scores(scores) {}
protected:
  virtual bool lessThan(Clause* c1,Clause* c2) {
    auto sc1 = _scores.get(c1);
    auto sc2 = _scores.get(c2);
    // reversing the order here: NNs think large is good, queues think small is good
    if (sc1 > sc2) {
      return true;
    }
    if (sc1 < sc2) {
      return false;
    }

    // TODO: could collect clause's literal's getId's to cheaply get more randomness with randomTraversals

    return c1->number() < c2->number();
  }
private:
  const DHMap<Clause*,double>& _scores;
};

class LRSIgnoringPassiveClauseContainer
: public PassiveClauseContainer
{
public:
  LRSIgnoringPassiveClauseContainer(bool isOutermost, const Shell::Options& opt) : PassiveClauseContainer(isOutermost,opt) {}
  virtual ~LRSIgnoringPassiveClauseContainer() {}

  /*
   * LRS specific methods for computation of Limits
   */
public:
  void simulationInit() override { NOT_IMPLEMENTED; }
  bool simulationHasNext() override { return false; }
  void simulationPopSelected() override { NOT_IMPLEMENTED; }

  // returns whether at least one of the limits was tightened
  bool setLimitsToMax() override { return false; }
  // returns whether at least one of the limits was tightened
  bool setLimitsFromSimulation() override { return false; }

  void onLimitsUpdated() override { NOT_IMPLEMENTED; }

  /*
   * LRS specific methods and fields for usage of limits
   */
  bool ageLimited() const override { return false; }
  bool weightLimited() const override { return false; }

  bool fulfilsAgeLimit(Clause* c) const override { return true; }
  // note: w here denotes the weight as returned by weight().
  // this method internally takes care of computing the corresponding weightForClauseSelection.

  bool fulfilsAgeLimit(unsigned w, unsigned numPositiveLiterals, const Inference& inference) const override { return true; }
  bool fulfilsWeightLimit(Clause* cl) const override { return true; }
  // note: w here denotes the weight as returned by weight().
  // this method internally takes care of computing the corresponding weightForClauseSelection.
  bool fulfilsWeightLimit(unsigned w, unsigned numPositiveLiterals, const Inference& inference) const override { return true; }

  bool childrenPotentiallyFulfilLimits(Clause* cl, unsigned upperBoundNumSelLits) const override { return true; }  
};

class LearnedPassiveClauseContainer
: public LRSIgnoringPassiveClauseContainer
{
protected:
  virtual double scoreClause(Clause*) = 0;
public:
  CLASS_NAME(LearnedPassiveClauseContainer);
  USE_ALLOCATOR(LearnedPassiveClauseContainer);

  LearnedPassiveClauseContainer(bool isOutermost, const Shell::Options& opt);
  virtual ~LearnedPassiveClauseContainer() {}

  unsigned sizeEstimate() const override { return _size; }
  bool isEmpty() const override { return _size == 0; }

  void add(Clause* cl) override;
  void remove(Clause* cl) override;
  Clause* popSelected() override;
private:
  DHMap<Clause*,double> _scores;
  ScoreQueue _queue;
  unsigned _size;
  double _temperature;
};

/**
 * 
 * 
 */
class NeuralPassiveClauseContainer
: public LRSIgnoringPassiveClauseContainer
{
public:
  CLASS_NAME(NeuralPassiveClauseContainer);
  USE_ALLOCATOR(NeuralPassiveClauseContainer);

  NeuralPassiveClauseContainer(bool isOutermost, const Shell::Options& opt);
  virtual ~NeuralPassiveClauseContainer(){}

  unsigned sizeEstimate() const override { return _size; }
  bool isEmpty() const override { return _size == 0; }
  void add(Clause* cl) override;
  void remove(Clause* cl) override;

  Clause* popSelected() override;

private:
  DHSet<Clause*> _known;
  DHMap<unsigned,Clause*> _clausesById;
  torch::jit::script::Module _model;
  unsigned _size;
  double _temperature;
};

/**
 * Defines the class Passive of passive clauses
 * @since 31/12/2007 Manchester
 */
class AWPassiveClauseContainer
: public PassiveClauseContainer
{
public:
  CLASS_NAME(AWPassiveClauseContainer);
  USE_ALLOCATOR(AWPassiveClauseContainer);

  AWPassiveClauseContainer(bool isOutermost, const Shell::Options& opt, vstring name);
  ~AWPassiveClauseContainer();
  void add(Clause* cl) override;

  void remove(Clause* cl) override;

  bool byWeight(int balance);

  Clause* popSelected() override;
  /** True if there are no passive clauses */
  bool isEmpty() const override
  { return _ageQueue.isEmpty() && _weightQueue.isEmpty(); }

  unsigned sizeEstimate() const override { return _size; }

  static Comparison compareWeight(Clause* cl1, Clause* cl2, const Shell::Options& opt);

private:
  /** The age queue, empty if _ageRatio=0 */
  AgeQueue _ageQueue;
  /** The weight queue, empty if _weightRatio=0 */
  WeightQueue _weightQueue;
  /** the age ratio */
  int _ageRatio;
  /** the weight ratio */
  int _weightRatio;
  /** current balance. If &lt;0 then selection by age, if &gt;0
   * then by weight */
  int _balance;

  unsigned _size;

  /*
   * LRS specific methods and fields for computation of Limits
   */
public:
  void simulationInit() override;
  bool simulationHasNext() override;
  void simulationPopSelected() override;

  // returns whether at least one of the limits was tightened
  bool setLimitsToMax() override;
  // returns whether at least one of the limits was tightened
  bool setLimitsFromSimulation() override;

  void onLimitsUpdated() override;
private:
  bool setLimits(unsigned newAgeSelectionMaxAge, unsigned newAgeSelectionMaxWeight, unsigned newWeightSelectionMaxWeight, unsigned newWeightSelectionMaxAge);

  int _simulationBalance;
  ClauseQueue::Iterator _simulationCurrAgeIt;
  ClauseQueue::Iterator _simulationCurrWeightIt;
  Clause* _simulationCurrAgeCl;
  Clause* _simulationCurrWeightCl;

  unsigned _ageSelectionMaxAge;
  unsigned _ageSelectionMaxWeight;
  unsigned _weightSelectionMaxWeight;
  unsigned _weightSelectionMaxAge;

  /*
   * LRS specific methods and fields for usage of limits
   */
public:
  bool ageLimited() const override;
  bool weightLimited() const override;

  bool fulfilsAgeLimit(Clause* c) const override;
  // note: w here denotes the weight as returned by weight().
  // age is to be recovered from inference
  // this method internally takes care of computing the corresponding weightForClauseSelection.
  bool fulfilsAgeLimit(unsigned w, unsigned numPositiveLiterals, const Inference& inference) const override;
  bool fulfilsWeightLimit(Clause* cl) const override;
  // note: w here denotes the weight as returned by weight().
  // age is to be recovered from inference
  // this method internally takes care of computing the corresponding weightForClauseSelection.
  bool fulfilsWeightLimit(unsigned w, unsigned numPositiveLiterals, const Inference& inference) const override;

  bool childrenPotentiallyFulfilLimits(Clause* cl, unsigned upperBoundNumSelLits) const override;
  
}; // class AWPassiveClauseContainer

/**
 * Light-weight version of the AWPassiveClauseContainer that
 * is not linked to the SaturationAlgorithm
 */
class AWClauseContainer: public ClauseContainer
{
public:
  AWClauseContainer(const Shell::Options& opt);

  void add(Clause* cl);
  bool remove(Clause* cl);

  /**
   * Set age-weight ratio
   * @since 08/01/2008 flight Murcia-Manchester
   */
  void setAgeWeightRatio(int age,int weight)
  {
    ASS(age >= 0);
    ASS(weight >= 0);
    ASS(age > 0 || weight > 0);

    _ageRatio = age;
    _weightRatio = weight;
  }

  Clause* popSelected();
  /** True if there are no passive clauses */
  bool isEmpty() const;

  unsigned size() const { return _size; }

  static Comparison compareWeight(Clause* cl1, Clause* cl2);

private:
  /** The age queue, empty if _ageRatio=0 */
  AgeQueue _ageQueue;
  /** The weight queue, empty if _weightRatio=0 */
  WeightQueue _weightQueue;
  /** the age ratio */
  int _ageRatio;
  /** the weight ratio */
  int _weightRatio;
  /** current balance. If &lt;0 then selection by age, if &gt;0
   * then by weight */
  int _balance;

  unsigned _size;

  bool _randomized;
};


};

#endif /* __AWPassiveClauseContainer__ */
