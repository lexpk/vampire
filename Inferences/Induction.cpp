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
 * @file Induction.cpp
 * Implements class Induction.
 */

#include <utility>

#include "Debug/RuntimeStatistics.hpp"

#include "Indexing/Index.hpp"
#include "Indexing/IndexManager.hpp"
#include "Indexing/LiteralSubstitutionTree.hpp"
#include "Indexing/ResultSubstitution.hpp"

#include "Inferences/BinaryResolution.hpp"

#include "Lib/DHSet.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/ScopedPtr.hpp"
#include "Lib/Set.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Connective.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/InterpretedLiteralEvaluator.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/OperatorType.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Unit.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/NewCNF.hpp"
#include "Shell/NNF.hpp"
#include "Shell/Rectify.hpp"

#include "Induction.hpp"

using std::pair;
using std::make_pair;

namespace Inferences
{
using namespace Kernel;
using namespace Lib; 

namespace {

void addToMapFromIterator(DHMap<Term*, TermQueryResult>& map, TermQueryResultIterator it) {
  while (it.hasNext()) {
    TermQueryResult tqr = it.next();
    ASS(tqr.term.isTerm());
    map.insert(tqr.term.term(), tqr);
  }
}

InferenceRule getGeneralizedRule(InferenceRule rule) {
  switch (rule) {
    case InferenceRule::INDUCTION_AXIOM:
    case InferenceRule::GEN_INDUCTION_AXIOM:
      return InferenceRule::GEN_INDUCTION_AXIOM;
    case InferenceRule::INT_INF_UP_INDUCTION_AXIOM:
    case InferenceRule::INT_INF_UP_GEN_INDUCTION_AXIOM:
      return InferenceRule::INT_INF_UP_GEN_INDUCTION_AXIOM;
    case InferenceRule::INT_INF_DOWN_INDUCTION_AXIOM:
    case InferenceRule::INT_INF_DOWN_GEN_INDUCTION_AXIOM:
      return InferenceRule::INT_INF_DOWN_GEN_INDUCTION_AXIOM;
    case InferenceRule::INT_FIN_UP_INDUCTION_AXIOM:
    case InferenceRule::INT_FIN_UP_GEN_INDUCTION_AXIOM:
      return InferenceRule::INT_FIN_UP_GEN_INDUCTION_AXIOM;
    case InferenceRule::INT_FIN_DOWN_INDUCTION_AXIOM:
    case InferenceRule::INT_FIN_DOWN_GEN_INDUCTION_AXIOM:
      return InferenceRule::INT_FIN_DOWN_GEN_INDUCTION_AXIOM;
    case InferenceRule::INT_DB_UP_INDUCTION_AXIOM:
    case InferenceRule::INT_DB_UP_GEN_INDUCTION_AXIOM:
      return InferenceRule::INT_DB_UP_GEN_INDUCTION_AXIOM;
    case InferenceRule::INT_DB_DOWN_INDUCTION_AXIOM:
    case InferenceRule::INT_DB_DOWN_GEN_INDUCTION_AXIOM:
      return InferenceRule::INT_DB_DOWN_GEN_INDUCTION_AXIOM;
    default:
      ASSERTION_VIOLATION;
  }
}

InferenceRule getNonGeneralizedRule(InferenceRule rule) {
  switch (rule) {
    case InferenceRule::INDUCTION_AXIOM:
    case InferenceRule::GEN_INDUCTION_AXIOM:
      return InferenceRule::INDUCTION_AXIOM;
    case InferenceRule::INT_INF_UP_INDUCTION_AXIOM:
    case InferenceRule::INT_INF_UP_GEN_INDUCTION_AXIOM:
      return InferenceRule::INT_INF_UP_INDUCTION_AXIOM;
    case InferenceRule::INT_INF_DOWN_INDUCTION_AXIOM:
    case InferenceRule::INT_INF_DOWN_GEN_INDUCTION_AXIOM:
      return InferenceRule::INT_INF_DOWN_INDUCTION_AXIOM;
    case InferenceRule::INT_FIN_UP_INDUCTION_AXIOM:
    case InferenceRule::INT_FIN_UP_GEN_INDUCTION_AXIOM:
      return InferenceRule::INT_FIN_UP_INDUCTION_AXIOM;
    case InferenceRule::INT_FIN_DOWN_INDUCTION_AXIOM:
    case InferenceRule::INT_FIN_DOWN_GEN_INDUCTION_AXIOM:
      return InferenceRule::INT_FIN_DOWN_INDUCTION_AXIOM;
    case InferenceRule::INT_DB_UP_INDUCTION_AXIOM:
    case InferenceRule::INT_DB_UP_GEN_INDUCTION_AXIOM:
      return InferenceRule::INT_DB_UP_INDUCTION_AXIOM;
    case InferenceRule::INT_DB_DOWN_INDUCTION_AXIOM:
    case InferenceRule::INT_DB_DOWN_GEN_INDUCTION_AXIOM:
      return InferenceRule::INT_DB_DOWN_INDUCTION_AXIOM;
    default:
      ASSERTION_VIOLATION;
  }
}

InferenceRule getInfRule(InferenceRule rule) {
  switch (rule) {
    case InferenceRule::INT_INF_UP_INDUCTION_AXIOM:
    case InferenceRule::INT_FIN_UP_INDUCTION_AXIOM:
    case InferenceRule::INT_DB_UP_INDUCTION_AXIOM:
      return InferenceRule::INT_INF_UP_INDUCTION_AXIOM;
    case InferenceRule::INT_INF_UP_GEN_INDUCTION_AXIOM:
    case InferenceRule::INT_FIN_UP_GEN_INDUCTION_AXIOM:
    case InferenceRule::INT_DB_UP_GEN_INDUCTION_AXIOM:
      return InferenceRule::INT_INF_UP_GEN_INDUCTION_AXIOM;
    case InferenceRule::INT_INF_DOWN_INDUCTION_AXIOM:
    case InferenceRule::INT_FIN_DOWN_INDUCTION_AXIOM:
    case InferenceRule::INT_DB_DOWN_INDUCTION_AXIOM:
      return InferenceRule::INT_INF_DOWN_INDUCTION_AXIOM;
    case InferenceRule::INT_INF_DOWN_GEN_INDUCTION_AXIOM:
    case InferenceRule::INT_FIN_DOWN_GEN_INDUCTION_AXIOM:
    case InferenceRule::INT_DB_DOWN_GEN_INDUCTION_AXIOM:
      return InferenceRule::INT_INF_DOWN_GEN_INDUCTION_AXIOM;
    default:
      ASSERTION_VIOLATION;
  }
}

InferenceRule getFinRule(InferenceRule rule) {
  switch (rule) {
    case InferenceRule::INT_INF_UP_INDUCTION_AXIOM:
    case InferenceRule::INT_FIN_UP_INDUCTION_AXIOM:
    case InferenceRule::INT_DB_UP_INDUCTION_AXIOM:
      return InferenceRule::INT_FIN_UP_INDUCTION_AXIOM;
    case InferenceRule::INT_INF_UP_GEN_INDUCTION_AXIOM:
    case InferenceRule::INT_FIN_UP_GEN_INDUCTION_AXIOM:
    case InferenceRule::INT_DB_UP_GEN_INDUCTION_AXIOM:
      return InferenceRule::INT_FIN_UP_GEN_INDUCTION_AXIOM;
    case InferenceRule::INT_INF_DOWN_INDUCTION_AXIOM:
    case InferenceRule::INT_FIN_DOWN_INDUCTION_AXIOM:
    case InferenceRule::INT_DB_DOWN_INDUCTION_AXIOM:
      return InferenceRule::INT_FIN_DOWN_INDUCTION_AXIOM;
    case InferenceRule::INT_INF_DOWN_GEN_INDUCTION_AXIOM:
    case InferenceRule::INT_FIN_DOWN_GEN_INDUCTION_AXIOM:
    case InferenceRule::INT_DB_DOWN_GEN_INDUCTION_AXIOM:
      return InferenceRule::INT_FIN_DOWN_GEN_INDUCTION_AXIOM;
    default:
      ASSERTION_VIOLATION;
  }
}

InferenceRule getDBRule(InferenceRule rule) {
  switch (rule) {
    case InferenceRule::INT_INF_UP_INDUCTION_AXIOM:
    case InferenceRule::INT_FIN_UP_INDUCTION_AXIOM:
    case InferenceRule::INT_DB_UP_INDUCTION_AXIOM:
      return InferenceRule::INT_DB_UP_INDUCTION_AXIOM;
    case InferenceRule::INT_INF_UP_GEN_INDUCTION_AXIOM:
    case InferenceRule::INT_FIN_UP_GEN_INDUCTION_AXIOM:
    case InferenceRule::INT_DB_UP_GEN_INDUCTION_AXIOM:
      return InferenceRule::INT_DB_UP_GEN_INDUCTION_AXIOM;
    case InferenceRule::INT_INF_DOWN_INDUCTION_AXIOM:
    case InferenceRule::INT_FIN_DOWN_INDUCTION_AXIOM:
    case InferenceRule::INT_DB_DOWN_INDUCTION_AXIOM:
      return InferenceRule::INT_DB_DOWN_INDUCTION_AXIOM;
    case InferenceRule::INT_INF_DOWN_GEN_INDUCTION_AXIOM:
    case InferenceRule::INT_FIN_DOWN_GEN_INDUCTION_AXIOM:
    case InferenceRule::INT_DB_DOWN_GEN_INDUCTION_AXIOM:
      return InferenceRule::INT_DB_DOWN_GEN_INDUCTION_AXIOM;
    default:
      ASSERTION_VIOLATION;
  }
}

};  // namespace

TermList TermReplacement::transformSubterm(TermList trm)
{
  CALL("TermReplacement::transformSubterm");

  if(trm.isTerm() && trm.term()==_o){
    return _r;
  }
  return trm;
}

TermList SkolemSquashingTermReplacement::transformSubterm(TermList trm)
{
  CALL("SkolemSquashingTermReplacement::transformSubterm");

  if(trm.isTerm()) {
    auto t = trm.term();
    if (t==_o){
      return _r;
    }
    unsigned f = t->functor();
    if (env.signature->getFunction(f)->skolem()) {
      unsigned v;
      if (!_tv.find(t,v)) {
        v = _v++;
        _tv.insert(t,v);
      }
      return TermList(v,false);
    }
  }
  return trm;
}

Literal* replaceTermInLiteral(Literal* lit, Term* o, TermList r) {
  TermReplacement tr(o,r);
  return tr.transform(lit);
}

Literal* replaceTermAndSquashSkolemsInLiteral(Literal* lit, Term* o, TermList r, unsigned& var, VList** varList = nullptr) {
  const bool strengthenHyp = env.options->inductionStrengthenHypothesis();
  if (!strengthenHyp) {
    return replaceTermInLiteral(lit, o, r);
  }
  SkolemSquashingTermReplacement tr(o,r,var);
  if (varList) {
    // The variables replacing the Skolems after calling transform
    // are needed for quantification if varList is non-null, collect them
    unsigned temp = var;
    auto res = tr.transform(lit);
    for (unsigned i = temp; i < var; i++) {
      VList::push(i,*varList);
    }
    return res;
  }
  return tr.transform(lit);
}

TermList LiteralSubsetReplacement::transformSubterm(TermList trm)
{
  CALL("LiteralSubsetReplacement::transformSubterm");

  if(trm.isTerm() && trm.term() == _o){
    // Replace either if there are too many occurrences to try all possibilities,
    // or if the bit in _iteration corresponding to this match is set to 1.
    if ((_occurrences > _maxOccurrences) || (1 & (_iteration >> _matchCount++))) {
      return _r;
    }
  }
  return trm;
}

Literal* LiteralSubsetReplacement::transformSubset(InferenceRule& rule) {
  CALL("LiteralSubsetReplacement::transformSubset");
  // Increment _iteration, since it either is 0, or was already used.
  _iteration++;
  // Note: __builtin_popcount() is a GCC built-in function.
  unsigned setBits = __builtin_popcount(_iteration);
  // Skip this iteration if not all bits are set, but more than maxSubset are set.
  while ((_iteration <= _maxIterations) &&
         ((_maxSubsetSize > 0) && (setBits < _occurrences) && (setBits > _maxSubsetSize))) {
    _iteration++;
    setBits = __builtin_popcount(_iteration);
  }
  if ((_iteration >= _maxIterations) ||
      ((_occurrences > _maxOccurrences) && (_iteration > 1))) {
    // All combinations were already returned.
    return nullptr;
  }
  if (setBits == _occurrences) {
    rule = getNonGeneralizedRule(rule);
  } else {
    rule = getGeneralizedRule(rule);
  }
  _matchCount = 0;
  return transform(_lit);
}

List<pair<Literal*, bool /*isGeneralized*/>>* LiteralSubsetReplacement::getListOfTransformedLiterals() {
  CALL("LiteralSubsetReplacement::getListOfTransformedLiterals");

  Literal* l;
  List<pair<Literal*, bool>>* res = List<pair<Literal*, bool>>::empty();
  InferenceRule rule = InferenceRule::INDUCTION_AXIOM;
  while ((l = transformSubset(rule))) {
    res = List<pair<Literal*, bool>>::cons(make_pair(l, rule == InferenceRule::GEN_INDUCTION_AXIOM), res);
  }
  return res;
}

void Induction::attach(SaturationAlgorithm* salg) {
  CALL("Induction::attach");

  GeneratingInferenceEngine::attach(salg);
  if (InductionHelper::isIntInductionOneOn()) {
    _comparisonIndex = static_cast<LiteralIndex*>(_salg->getIndexManager()->request(UNIT_INT_COMPARISON_INDEX));
    _inductionTermIndex = static_cast<TermIndex*>(_salg->getIndexManager()->request(INDUCTION_TERM_INDEX));
  }
}

void Induction::detach() {
  CALL("Induction::detach");

  if (InductionHelper::isIntInductionOneOn()) {
    _comparisonIndex = nullptr;
    _salg->getIndexManager()->release(UNIT_INT_COMPARISON_INDEX);
    _inductionTermIndex = nullptr;
    _salg->getIndexManager()->release(INDUCTION_TERM_INDEX);
  }
  GeneratingInferenceEngine::detach();
}

ClauseIterator Induction::generateClauses(Clause* premise)
{
  CALL("Induction::generateClauses");

  return pvi(InductionClauseIterator(premise, InductionHelper(_comparisonIndex, _inductionTermIndex, _salg->getSplitter()), getOptions()));
}

void InductionClauseIterator::processClause(Clause* premise)
{
  CALL("InductionClauseIterator::processClause");

  // The premise should either contain a literal on which we want to apply induction,
  // or it should be an integer constant comparison we use as a bound.
  if (InductionHelper::isInductionClause(premise)) {
    for (unsigned i=0;i<premise->length();i++) {
      processLiteral(premise,(*premise)[i]);
    }
  }
  if (InductionHelper::isIntInductionOneOn() && InductionHelper::isIntegerComparison(premise)) {
    processIntegerComparison(premise, (*premise)[0]);
  }
}

void InductionClauseIterator::processLiteral(Clause* premise, Literal* lit)
{
  CALL("Induction::ClauseIterator::processLiteral");

  if(_opt.showInduction()){
    env.beginOutput();
    env.out() << "[Induction] process " << lit->toString() << " in " << premise->toString() << endl;
    env.endOutput();
  }

  static bool generalize = _opt.inductionGen();

  if(InductionHelper::isInductionLiteral(lit)){
      Set<Term*> ta_terms;
      Set<Term*> int_terms;
      //TODO this should be a non-variable non-type iterator it seems
      SubtermIterator it(lit);
      while(it.hasNext()){
        TermList ts = it.next();
        if(!ts.isTerm()){ continue; }
        unsigned f = ts.term()->functor(); 
        if(InductionHelper::isInductionTermFunctor(f)){
          if(InductionHelper::isStructInductionOn() && InductionHelper::isStructInductionFunctor(f)){
            ta_terms.insert(ts.term());
          }
          if(InductionHelper::isIntInductionOneOn() && InductionHelper::isIntInductionTermListInLiteral(ts, lit)){
            int_terms.insert(ts.term());
          }
        }
      }

      Set<Term*>::Iterator citer1(int_terms);
      while(citer1.hasNext()){
        Term* t = citer1.next();
        Term* indTerm = generalize ? getPlaceholderForTerm(t) : t;
        List<pair<Literal*, bool /*isGeneralized*/>>* indLits = List<pair<Literal*, bool>>::empty();
        DHMap<Term*, TermQueryResult> grBound;
        addToMapFromIterator(grBound, _helper.getGreaterEqual(t));
        addToMapFromIterator(grBound, _helper.getGreater(t));
        DHMap<Term*, TermQueryResult> leBound;
        addToMapFromIterator(leBound, _helper.getLessEqual(t));
        addToMapFromIterator(leBound, _helper.getLess(t));
        performIntInductionForEligibleBounds(premise, lit, t, indLits, indTerm, /*increasing=*/true, leBound, grBound);
        performIntInductionForEligibleBounds(premise, lit, t, indLits, indTerm, /*increasing=*/false, grBound, leBound);
        List<pair<Literal*, bool>>::destroy(indLits);
      }
      Set<Term*>::Iterator citer2(ta_terms);
      while(citer2.hasNext()){
        Term* t = citer2.next();
        static bool one = _opt.structInduction() == Options::StructuralInductionKind::ONE ||
                          _opt.structInduction() == Options::StructuralInductionKind::ALL;
        static bool two = _opt.structInduction() == Options::StructuralInductionKind::TWO ||
                          _opt.structInduction() == Options::StructuralInductionKind::ALL;
        static bool three = _opt.structInduction() == Options::StructuralInductionKind::THREE ||
                          _opt.structInduction() == Options::StructuralInductionKind::ALL;
        if(notDone(lit,t)){
          InferenceRule rule = InferenceRule::INDUCTION_AXIOM;
          Term* inductionTerm = generalize ? getPlaceholderForTerm(t) : t;
          Kernel::LiteralSubsetReplacement subsetReplacement(lit, t, TermList(inductionTerm), _opt.maxInductionGenSubsetSize());
          Literal* ilit = generalize ? subsetReplacement.transformSubset(rule) : lit;
          ASS(ilit != nullptr);
          do {
            if(one){
              performStructInductionOne(premise,lit,ilit,inductionTerm,rule);
            }
            if(two){
              performStructInductionTwo(premise,lit,ilit,inductionTerm,rule);
            }
            if(three){
              performStructInductionThree(premise,lit,ilit,inductionTerm,rule);
            }
          } while (generalize && (ilit = subsetReplacement.transformSubset(rule)));
        }
      } 
   }
}

void InductionClauseIterator::performIntInductionForEligibleBounds(Clause* premise, Literal* origLit, Term* origTerm, List<pair<Literal*, bool /*isGeneralized*/>>*& indLits, Term* indTerm, bool increasing, DHMap<Term*, TermQueryResult>& bounds1, DHMap<Term*, TermQueryResult>& bounds2) {
  DHMap<Term*, TermQueryResult>::Iterator it1(bounds1);
  while (it1.hasNext()) {
    TermQueryResult b1 = it1.next();
    // Skip if the premise equals the bound (that would add tautologies to the search space).
    if (b1.clause != premise) {
      if (_helper.isInductionForFiniteIntervalsOn()) {
        DHMap<Term*, TermQueryResult>::Iterator it2(bounds2);
        while (it2.hasNext()) {
          TermQueryResult b2 = it2.next();
          if ((b2.clause != premise) &&
              notDoneInt(origLit, origTerm, increasing, b1.term.term(), b2.term.term(), /*bool fromComparison=*/b1.literal != nullptr)) {
            generalizeAndPerformIntInduction(premise, origLit, origTerm, indLits, indTerm, increasing, b1, &b2);
          }
        }
      }
      if (_helper.isInductionForInfiniteIntervalsOn() &&
          notDoneInt(origLit, origTerm, increasing, b1.term.term(), /*optionalBound2=*/nullptr, /*bool fromComparison=*/b1.literal != nullptr)) {
        generalizeAndPerformIntInduction(premise, origLit, origTerm, indLits, indTerm, increasing, b1, nullptr);
      }
    }
  }
  static bool useDefaultBound = _opt.integerInductionDefaultBound();
  if (useDefaultBound && _helper.isInductionForInfiniteIntervalsOn()) {
    static TermQueryResult defaultBound(TermList(theory->representConstant(IntegerConstantType(0))), nullptr, nullptr);
    if (notDoneInt(origLit, origTerm, increasing, defaultBound.term.term(), /*optionalBound2=*/nullptr, /*fromComparison=*/false)) {
      generalizeAndPerformIntInduction(premise, origLit, origTerm, indLits, indTerm, increasing, defaultBound, nullptr);
    }
  }
}

void InductionClauseIterator::generalizeAndPerformIntInduction(Clause* premise, Literal* origLit, Term* origTerm, List<pair<Literal*, bool /*isGeneralized*/>>*& indLits, Term* indTerm, bool increasing, TermQueryResult& bound1, TermQueryResult* optionalBound2) {
  static bool generalize = _opt.inductionGen();
  // If induction literals were not computed yet, compute them now.
  if (List<pair<Literal*, bool>>::isEmpty(indLits)) {
    if (generalize) {
      Kernel::LiteralSubsetReplacement subsetReplacement(origLit, origTerm, TermList(indTerm), _opt.maxInductionGenSubsetSize());
      indLits = subsetReplacement.getListOfTransformedLiterals();
    } else {
      indLits = new List<pair<Literal*, bool /*isGeneralized*/>>(make_pair(origLit, false));
    }
  }
  bool finite = ((optionalBound2 != nullptr) && (optionalBound2->literal != nullptr));
  InferenceRule rule = 
      (bound1.literal == nullptr)
          ? (increasing ? InferenceRule::INT_DB_UP_INDUCTION_AXIOM : InferenceRule::INT_DB_DOWN_INDUCTION_AXIOM)
          : (increasing ? (finite ? InferenceRule::INT_FIN_UP_INDUCTION_AXIOM : InferenceRule::INT_INF_UP_INDUCTION_AXIOM)
                        : (finite ? InferenceRule::INT_FIN_DOWN_INDUCTION_AXIOM : InferenceRule::INT_INF_DOWN_INDUCTION_AXIOM));
  List<pair<Literal*, bool>>::RefIterator it(indLits);
  while (it.hasNext()) {
    auto& litAndIsGen = it.next();
    ASS(litAndIsGen.first != nullptr);
    performIntInduction(premise, origLit, litAndIsGen.first, indTerm, litAndIsGen.second ? getGeneralizedRule(rule) : rule, increasing, bound1, optionalBound2);
  }
}

void InductionClauseIterator::processIntegerComparison(Clause* premise, Literal* lit)
{
  CALL("Induction::ClauseIterator::processIntegerComparison");

  ASS((theory->interpretPredicate(lit) == Theory::INT_LESS) && lit->ground());

  bool positive = lit->isPositive();
  TermList* lesserTL = lit->nthArgument(positive ? 0 : 1);
  TermList* greaterTL = lit->nthArgument(positive ? 1 : 0);
  ASS(lesserTL != nullptr);
  ASS(greaterTL != nullptr);
  Term* lt = lesserTL->term();
  Term* gt = greaterTL->term();
  static bool generalize = _opt.inductionGen();
  DHMap<Term*, TermQueryResult> grBound;
  addToMapFromIterator(grBound, _helper.getGreaterEqual(gt));
  addToMapFromIterator(grBound, _helper.getGreater(gt));
  performIntInductionOnEligibleLiterals(
    gt, generalize ? getPlaceholderForTerm(gt) : gt, _helper.getTQRsForInductionTerm(*greaterTL), /*increasing=*/true, TermQueryResult(*lesserTL, lit, premise), grBound);
  DHMap<Term*, TermQueryResult> leBound;
  addToMapFromIterator(leBound, _helper.getLessEqual(lt));
  addToMapFromIterator(leBound, _helper.getLess(lt));
  performIntInductionOnEligibleLiterals(
    lt, generalize ? getPlaceholderForTerm(lt) : lt, _helper.getTQRsForInductionTerm(*lesserTL), /*increasing=*/false, TermQueryResult(*greaterTL, lit, premise), leBound);
}

void InductionClauseIterator::performIntInductionOnEligibleLiterals(Term* origTerm, Term* indTerm, TermQueryResultIterator inductionTQRsIt, bool increasing, TermQueryResult bound1, DHMap<Term*, TermQueryResult>& bounds2) {
  while (inductionTQRsIt.hasNext()) {
    TermQueryResult tqr = inductionTQRsIt.next();
    // Skip if the TQR clause is equal to the bound clause (that would add tautologies to the search space).
    if (bound1.clause != tqr.clause) {
      // We need to pass an empty list, which will get populated when performing induction.
      // Then we need to destroy it.
      List<pair<Literal*, bool /*isGeneralized*/>>* indLits = List<pair<Literal*, bool>>::empty();
      if (_helper.isInductionForFiniteIntervalsOn()) {
        DHMap<Term*, TermQueryResult>::Iterator it(bounds2);
        while (it.hasNext()) {
          TermQueryResult bound2 = it.next();
          if ((bound2.clause != tqr.clause) &&
              notDoneInt(tqr.literal, origTerm, increasing, bound1.term.term(), bound2.term.term(), /*bool fromComparison=*/bound1.literal != nullptr)) {
            generalizeAndPerformIntInduction(tqr.clause, tqr.literal, origTerm, indLits, indTerm, increasing, bound1, &bound2);
          }
        }
      }
      if (_helper.isInductionForInfiniteIntervalsOn() &&
          notDoneInt(tqr.literal, origTerm, increasing, bound1.term.term(), /*optionalBound2=*/nullptr, /*bool fromComparison=*/bound1.literal != nullptr)) {
        generalizeAndPerformIntInduction(tqr.clause, tqr.literal, origTerm, indLits, indTerm, increasing, bound1, nullptr);
      }
      List<pair<Literal*, bool>>::destroy(indLits);
    }
  }
}

void InductionClauseIterator::produceClauses(Clause* premise, Literal* origLit, Formula* hypothesis, InferenceRule rule, const pair<Literal*, SLQueryResult>& conclusion)
{
  CALL("InductionClauseIterator::produceClauses");
  const List<pair<Literal*, SLQueryResult>> toResolve(conclusion);
  produceClauses(premise, origLit, hypothesis, rule, &toResolve);
}

void InductionClauseIterator::produceClauses(Clause* premise, Literal* origLit, Formula* hypothesis, InferenceRule rule, const List<pair<Literal*, SLQueryResult>>* toResolve)
{
  CALL("InductionClauseIterator::produceClauses");
  NewCNF cnf(0);
  cnf.setForInduction();
  Stack<Clause*> hyp_clauses;
  Inference inf = NonspecificInference0(UnitInputType::AXIOM,rule);
  inf.setInductionDepth(premise->inference().inductionDepth()+1);
  FormulaUnit* fu = new FormulaUnit(hypothesis,inf);
  cnf.clausify(NNF::ennf(fu), hyp_clauses);

  // Now, when possible, perform resolution against all literals from toResolve, which contain:
  // 1. the original literal,
  // 2. the bounds on the induction term (which are in the form "term < bound", or other comparison),
  // if hyp_clauses contain the literal(s).
  // (If hyp_clauses do not contain the literal(s), the clause is a definition from clausification
  // and just keep it as it is.)
  Stack<Clause*>::Iterator cit(hyp_clauses);
  while(cit.hasNext()){
    Clause* c = cit.next();
    bool resolved = false;
    List<pair<Literal*, SLQueryResult>>::RefIterator resIt(toResolve);
    while (resIt.hasNext()) {
      auto& litAndSLQR = resIt.next();
      // If litAndSLQR contains a literal present in the clause, resolve it.
      if(litAndSLQR.first && c->contains(litAndSLQR.first)){
        if (resolved) {
          // 'c' is never added to the saturation set, hence we need to call splitter here, before
          // we apply binary resolution on it.
          _helper.callSplitterOnNewClause(c);
        }
        c = BinaryResolution::generateClause(c,litAndSLQR.first,litAndSLQR.second,_opt);
        resolved = true;
      }
    }
    _clauses.push(c);
  }
  env.statistics->induction++;
  if (rule == InferenceRule::GEN_INDUCTION_AXIOM ||
      rule == InferenceRule::INT_INF_UP_GEN_INDUCTION_AXIOM ||
      rule == InferenceRule::INT_FIN_UP_GEN_INDUCTION_AXIOM ||
      rule == InferenceRule::INT_DB_UP_GEN_INDUCTION_AXIOM ||
      rule == InferenceRule::INT_INF_DOWN_GEN_INDUCTION_AXIOM ||
      rule == InferenceRule::INT_FIN_DOWN_GEN_INDUCTION_AXIOM ||
      rule == InferenceRule::INT_DB_DOWN_GEN_INDUCTION_AXIOM) {
    env.statistics->generalizedInduction++;
  }
  switch (rule) {
    case InferenceRule::INDUCTION_AXIOM:
    case InferenceRule::GEN_INDUCTION_AXIOM:
      env.statistics->structInduction++;
      break;
    case InferenceRule::INT_INF_UP_INDUCTION_AXIOM:
    case InferenceRule::INT_INF_UP_GEN_INDUCTION_AXIOM:
    case InferenceRule::INT_INF_DOWN_INDUCTION_AXIOM:
    case InferenceRule::INT_INF_DOWN_GEN_INDUCTION_AXIOM:
      env.statistics->intInfInduction++;
      break;
    case InferenceRule::INT_FIN_UP_INDUCTION_AXIOM:
    case InferenceRule::INT_FIN_UP_GEN_INDUCTION_AXIOM:
    case InferenceRule::INT_FIN_DOWN_INDUCTION_AXIOM:
    case InferenceRule::INT_FIN_DOWN_GEN_INDUCTION_AXIOM:
      env.statistics->intFinInduction++;
      break;
    case InferenceRule::INT_DB_UP_INDUCTION_AXIOM:
    case InferenceRule::INT_DB_UP_GEN_INDUCTION_AXIOM:
    case InferenceRule::INT_DB_DOWN_INDUCTION_AXIOM:
    case InferenceRule::INT_DB_DOWN_GEN_INDUCTION_AXIOM:
      env.statistics->intDBInduction++;
      break;
    default:
      ;
  }
  switch (rule) {
    case InferenceRule::INT_INF_UP_INDUCTION_AXIOM:
    case InferenceRule::INT_INF_UP_GEN_INDUCTION_AXIOM:
      env.statistics->intInfUpInduction++;
      break;
    case InferenceRule::INT_INF_DOWN_INDUCTION_AXIOM:
    case InferenceRule::INT_INF_DOWN_GEN_INDUCTION_AXIOM:
      env.statistics->intInfDownInduction++;
      break;
    case InferenceRule::INT_FIN_UP_INDUCTION_AXIOM:
    case InferenceRule::INT_FIN_UP_GEN_INDUCTION_AXIOM:
      env.statistics->intFinUpInduction++;
      break;
    case InferenceRule::INT_FIN_DOWN_INDUCTION_AXIOM:
    case InferenceRule::INT_FIN_DOWN_GEN_INDUCTION_AXIOM:
      env.statistics->intFinDownInduction++;
      break;
    case InferenceRule::INT_DB_UP_INDUCTION_AXIOM:
    case InferenceRule::INT_DB_UP_GEN_INDUCTION_AXIOM:
      env.statistics->intDBUpInduction++;
      break;
    case InferenceRule::INT_DB_DOWN_INDUCTION_AXIOM:
    case InferenceRule::INT_DB_DOWN_GEN_INDUCTION_AXIOM:
      env.statistics->intDBDownInduction++;
      break;
    default:
      ;
  }
}

// Given a literal ~L[term], where 'term' is of the integer sort,
// introduce and induction hypothesis for integers, for example:
//   (L[b1] & (![X] : (b1 <= X & X < b2 & L[X]) -> L[x+1])) -> (![Y] : (b1 <= Y & Y <= b2) -> L[Y])
// In general, the hypothesis is an instance of one of the following
// hypotheses (depending on the value of 'increasing'):
//   (L[b1] & (![X] : (interval_x(X)) -> L[x+1])) -> (![Y] : interval_y(Y) -> L[Y])
//   (L[b1] & (![X] : (interval_x(X)) -> L[x-1])) -> (![Y] : interval_y(Y) -> L[Y])
// where 'b1' is bound1.term, and the predicates inteval_x(X) and interval_y(Y)
// capture the property "X (or Y) belongs to the interval [b1, b2] or [b1, b2)",
// where 'b2' is either optionalBound2->term (if present) or depending on 'increasing'
// either infinity or -infinity. (The intervals are set such that the hypothesis
// is valid: if interval_y(Y) holds for some Y, then either interval_x(Y) holds,
// or depending on 'increasing' either interval_x(Y-1) or interval_x(Y+1) holds.)
void InductionClauseIterator::performIntInduction(Clause* premise, Literal* origLit, Literal* lit, Term* term, InferenceRule rule, bool increasing, const TermQueryResult& bound1, TermQueryResult* optionalBound2)
{
  CALL("InductionClauseIterator::performIntInduction");

  TermList b1(bound1.term);
  TermList one(theory->representConstant(IntegerConstantType(increasing ? 1 : -1)));

  TermList x(0,false);
  TermList y(1,false);

  Literal* clit = Literal::complementaryLiteral(lit);

  // create L[b1]
  Formula* Lb1 = new AtomicFormula(replaceTermInLiteral(clit,term,b1));

  // create L[X]
  Formula* Lx = new AtomicFormula(replaceTermInLiteral(clit,term,x));

  // create L[Y]
  Formula* Ly = new AtomicFormula(replaceTermInLiteral(clit,term,y));

  // create L[X+1] or L[X-1]
  TermList fpo(Term::create2(env.signature->getInterpretingSymbol(Theory::INT_PLUS),x,one));
  Formula* Lxpo = new AtomicFormula(replaceTermInLiteral(clit,term,fpo));

  static unsigned less = env.signature->getInterpretingSymbol(Theory::INT_LESS);
  // create X>=b1 (which is ~X<b1) or X<=b1 (which is ~b1<X)
  Formula* Lxcompb1 = new AtomicFormula(Literal::create2(less,false,(increasing ? x : b1),(increasing ? b1 : x)));
  // create Y>=b1 (which is ~Y<b1), or Y>b1, or Y<=b1 (which is ~b1<Y), or Y<b1
  // This comparison is mirroring the structure of bound1.literal, which is "b1 <comparison> inductionTerm".
  // If bound1.literal is nullptr, we are using the default bound with the comparison sign >= or <=.
  const bool isBound1Equal = (!bound1.literal || (bound1.literal->functor() == less && bound1.literal->isNegative()));
  const bool isBound1FirstArg = (increasing != isBound1Equal);
  Formula* Lycompb1 = new AtomicFormula(Literal::create2(
        less, !isBound1Equal, (isBound1FirstArg ? b1 : y), (isBound1FirstArg ? y : b1)));

  Formula* FxInterval;
  Formula* FyInterval;
  const bool isDefaultBound = ((bound1.clause == nullptr) || (bound1.literal == nullptr));
  const bool hasBound2 = ((optionalBound2 != nullptr) && (optionalBound2->literal != nullptr));
  if (hasBound2) {
    // Finite interval induction, use two bounds on both x and y.
    rule = getFinRule(rule);
    TermList b2(optionalBound2->term);
    // create X<b2 or X>b2 (which is b2<X)
    Formula* Lxcompb2 = new AtomicFormula(Literal::create2(less, true, (increasing ? x : b2), (increasing ? b2 : x)));
    const bool isBound2Equal = (optionalBound2->literal->functor() == less && optionalBound2->literal->isNegative());
    const bool isBound2FirstArg = (increasing == isBound2Equal);
    // create Y<b2, or Y<=b2 (which is ~b2<Y) or Y>b2, or Y>=b2 (which is ~Y<b2)
    Formula* Lycompb2 = new AtomicFormula(Literal::create2(
          less, !isBound2Equal, (isBound2FirstArg ? b2 : y), (isBound2FirstArg ? y : b2)));
    FxInterval = new JunctionFormula(Connective::AND, FormulaList::cons(Lxcompb1, FormulaList::singleton(Lxcompb2)));
    FyInterval = new JunctionFormula(Connective::AND, FormulaList::cons(Lycompb1, FormulaList::singleton(Lycompb2)));
  } else {
    // Infinite interval induction (either with default bound or not), use only one bound on both x and y.
    if (isDefaultBound) rule = getDBRule(rule);
    else rule = getInfRule(rule);
    FxInterval = Lxcompb1;
    FyInterval = Lycompb1;
  }

  // Create the hypothesis, with FxInterval and FyInterval being as described
  // in the comment above this function.
  Formula* hyp = new BinaryFormula(Connective::IMP,
                   new JunctionFormula(Connective::AND,FormulaList::cons(Lb1,FormulaList::singleton(
                     Formula::quantify(new BinaryFormula(Connective::IMP,
                       new JunctionFormula(Connective::AND, FormulaList::cons(FxInterval,FormulaList::singleton(Lx))),
                       Lxpo))))),
                   Formula::quantify(new BinaryFormula(Connective::IMP,FyInterval,Ly)));
  
  auto toResolve = List<pair<Literal*, SLQueryResult>>::empty();
  // Also resolve the hypothesis with comparisons with bound(s) (if the bound(s) are present/not default).
  if (!isDefaultBound) {
    // After resolving L[y], 'y' will be already substituted by 'term'.
    // Therefore, the second (and third) substitution(s) is/are empty.
    static ResultSubstitutionSP identity = ResultSubstitutionSP(new IdentitySubstitution());
    List<pair<Literal*, SLQueryResult>>::push(make_pair(
        Literal::complementaryLiteral(bound1.literal),
        SLQueryResult(bound1.literal, bound1.clause, identity)),
      toResolve);
    // If there is also a second bound, add that to the list as well.
    if (hasBound2) {
      List<pair<Literal*, SLQueryResult>>::push(make_pair(
          Literal::complementaryLiteral(optionalBound2->literal),
          SLQueryResult(optionalBound2->literal, optionalBound2->clause, identity)),
        toResolve);
    }
  }

  // Create pairs of Literal* and SLQueryResult for resolving L[y] and Y>=b (or Y<=b or Y>b or Y<b)
  static RobSubstitution subst;
  // When producing clauses, 'y' should be unified with 'term'
  ALWAYS(subst.unify(TermList(term), 0, y, 1));
  ResultSubstitutionSP resultSubst = ResultSubstitution::fromSubstitution(&subst, 1, 0);
  List<pair<Literal*, SLQueryResult>>::push(make_pair(
      Ly->literal(),
      SLQueryResult(origLit, premise, resultSubst)),
    toResolve);
  produceClauses(premise, lit, hyp, rule, toResolve);
  List<pair<Literal*, SLQueryResult>>::destroy(toResolve);
  subst.reset();
}

/**
 * Introduce the Induction Hypothesis
 * ( L[base1] & ... & L[basen] & (L[x] => L[c1(x)]) & ... (L[x] => L[cm(x)]) ) => L[x]
 * for some lit ~L[a]
 * and then force binary resolution on L for each resultant clause
 */

void InductionClauseIterator::performStructInductionOne(Clause* premise, Literal* origLit, Literal* lit, Term* term, InferenceRule rule)
{
  CALL("InductionClauseIterator::performStructInductionOne"); 

  TermAlgebra* ta = env.signature->getTermAlgebraOfSort(env.signature->getFunction(term->functor())->fnType()->result());
  TermList ta_sort = ta->sort();

  FormulaList* formulas = FormulaList::empty();

  Literal* clit = Literal::complementaryLiteral(lit);
  unsigned var = 0;

  // first produce the formula
  for(unsigned i=0;i<ta->nConstructors();i++){
    TermAlgebraConstructor* con = ta->constructor(i);
    unsigned arity = con->arity();
      Stack<TermList> argTerms;
      Stack<TermList> ta_vars;
      for(unsigned j=0;j<arity;j++){
        TermList x(var,false);
        var++;
        if(con->argSort(j) == ta_sort){
          ta_vars.push(x);
        }
        argTerms.push(x);
      }
      // if hypothesis strengthening is on, this replaces the Skolems with fresh variables
      Formula* right = new AtomicFormula(
        replaceTermAndSquashSkolemsInLiteral(clit,term,
        TermList(Term::create(con->functor(),(unsigned)argTerms.size(), argTerms.begin())), var));
      FormulaList* args = FormulaList::empty();
      Stack<TermList>::Iterator tvit(ta_vars);
      while(tvit.hasNext()){
        auto hypVars = VList::empty();
        Formula* hyp = new AtomicFormula(
          replaceTermAndSquashSkolemsInLiteral(clit,term,tvit.next(),var,&hypVars));
        // quantify each hypotheses with variables replacing Skolems explicitly
        if (hypVars) {
          hyp = new QuantifiedFormula(Connective::FORALL, hypVars, SList::empty(), hyp);
        }
        FormulaList::push(hyp,args);
      }
      FormulaList::push(args ?
        new BinaryFormula(Connective::IMP,JunctionFormula::generalJunction(Connective::AND,args),right) : right, formulas);
  }
  ASS(formulas);
  Formula* indPremise = JunctionFormula::generalJunction(Connective::AND,formulas);
  Literal* conclusion = replaceTermAndSquashSkolemsInLiteral(clit,term,TermList(var++,false),var);
  Formula* hypothesis = new BinaryFormula(Connective::IMP,
                            Formula::quantify(indPremise),
                            Formula::quantify(new AtomicFormula(conclusion)));

  static ResultSubstitutionSP identity = ResultSubstitutionSP(new IdentitySubstitution());
  pair<Literal*, SLQueryResult> toResolve(conclusion, SLQueryResult(origLit, premise, identity));
  produceClauses(premise, origLit, hypothesis, rule, toResolve);
}

/**
 * This idea (taken from the CVC4 paper) is that there exists some smallest k that makes lit true
 * We produce the clause ~L[x] \/ ?y : L[y] & !z (z subterm y -> ~L[z])
 * and perform resolution with lit L[c]
 */
void InductionClauseIterator::performStructInductionTwo(Clause* premise, Literal* origLit, Literal* lit, Term* term, InferenceRule rule) 
{
  CALL("InductionClauseIterator::performStructInductionTwo"); 

  TermAlgebra* ta = env.signature->getTermAlgebraOfSort(env.signature->getFunction(term->functor())->fnType()->result());
  TermList ta_sort = ta->sort();

  Literal* clit = Literal::complementaryLiteral(lit);

  // make L[y]
  TermList y(0,false); 
  unsigned var = 1;
  // if hypothesis strengthening is on, this replaces the Skolems with fresh variables
  auto mainVars = VList::singleton(y.var());
  Literal* Ly = replaceTermAndSquashSkolemsInLiteral(lit,term,y,var,&mainVars);

  // for each constructor and destructor make
  // ![Z] : y = cons(Z,dec(y)) -> ( ~L[dec1(y)] & ~L[dec2(y)]
  FormulaList* formulas = FormulaList::empty();

  for(unsigned i=0;i<ta->nConstructors();i++){
    TermAlgebraConstructor* con = ta->constructor(i);
    unsigned arity = con->arity();

    if(con->recursive()){
  
      // First generate all argTerms and remember those that are of sort ta_sort 
      Stack<TermList> argTerms;
      Stack<TermList> taTerms; 
      for(unsigned j=0;j<arity;j++){
        unsigned dj = con->destructorFunctor(j);
        TermList djy(Term::create1(dj,y));
        argTerms.push(djy);
        if(con->argSort(j) == ta_sort){
          taTerms.push(djy);
        }
      }
      ASS(taTerms.isNonEmpty());
      // create y = con1(...d1(y)...d2(y)...)
      TermList coni(Term::create(con->functor(),(unsigned)argTerms.size(), argTerms.begin()));
      Literal* kneq = Literal::createEquality(true,y,coni,ta_sort);
      FormulaList* And = FormulaList::empty(); 
      Stack<TermList>::Iterator tit(taTerms);
      while(tit.hasNext()){
        TermList djy = tit.next();
        auto hypVars = VList::empty();
        Literal* nLdjy = replaceTermAndSquashSkolemsInLiteral(clit,term,djy,var,&hypVars);
        Formula* f = new AtomicFormula(nLdjy); 
        if (hypVars) {
          f = new QuantifiedFormula(Connective::FORALL, hypVars, SList::empty(), f);
        }
        FormulaList::push(f,And);
      }
      ASS(And);
      Formula* imp = new BinaryFormula(Connective::IMP,
                            new AtomicFormula(kneq),
                            JunctionFormula::generalJunction(Connective::AND,And));
      FormulaList::push(imp,formulas);
    }
  }
  // quantify with mainVars explicitly
  Formula* exists = new QuantifiedFormula(Connective::EXISTS, mainVars,SList::empty(),
                        formulas ? new JunctionFormula(Connective::AND,FormulaList::cons(new AtomicFormula(Ly),formulas))
                                 : static_cast<Formula*>(new AtomicFormula(Ly)));
  
  Literal* conclusion = replaceTermAndSquashSkolemsInLiteral(clit,term,TermList(var++,false),var);
  FormulaList* orf = FormulaList::cons(exists,FormulaList::singleton(Formula::quantify(new AtomicFormula(conclusion))));
  Formula* hypothesis = new JunctionFormula(Connective::OR,orf);

  static ResultSubstitutionSP identity = ResultSubstitutionSP(new IdentitySubstitution());
  pair<Literal*, SLQueryResult> toResolve(conclusion, SLQueryResult(origLit, premise, identity));
  produceClauses(premise, origLit, hypothesis, rule, toResolve);
}

/*
 * A variant of Two where we are stronger with respect to all subterms. here the existential part is
 *
 * ?y : L[y] &_{con_i} ( y = con_i(..dec(y)..) -> smaller(dec(y))) 
             & (!x : smallerThanY(x) -> smallerThanY(destructor(x))) 
             & !z : smallerThanY(z) => ~L[z]
 *
 * i.e. we add a new special predicat that is true when its argument is smaller than Y
 *
 */
void InductionClauseIterator::performStructInductionThree(Clause* premise, Literal* origLit, Literal* lit, Term* term, InferenceRule rule) 
{
  CALL("InductionClauseIterator::performStructInductionThree");

  TermAlgebra* ta = env.signature->getTermAlgebraOfSort(env.signature->getFunction(term->functor())->fnType()->result());
  TermList ta_sort = ta->sort();

  Literal* clit = Literal::complementaryLiteral(lit);

  // make L[y]
  TermList x(0,false); 
  TermList y(1,false); 
  TermList z(2,false); 
  unsigned vars = 3;
  // if hypothesis strengthening is on, this replaces the Skolems with fresh variables
  auto mainVars = VList::singleton(y.var());
  Literal* Ly = replaceTermAndSquashSkolemsInLiteral(lit,term,y,vars,&mainVars);

  // make smallerThanY
  unsigned sty = env.signature->addFreshPredicate(1,"smallerThan");
  env.signature->getPredicate(sty)->setType(OperatorType::getPredicateType({ta_sort}));

  // make ( y = con_i(..dec(y)..) -> smaller(dec(y)))  for each constructor 
  FormulaList* conjunction = FormulaList::singleton(new AtomicFormula(Ly));
  for(unsigned i=0;i<ta->nConstructors();i++){
    TermAlgebraConstructor* con = ta->constructor(i);
    unsigned arity = con->arity();

    if(con->recursive()){
      // First generate all argTerms and remember those that are of sort ta_sort 
      Stack<TermList> argTerms;
      Stack<TermList> taTerms; 
      Stack<unsigned> ta_vars;
      Stack<TermList> varTerms;
      for(unsigned j=0;j<arity;j++){
        unsigned dj = con->destructorFunctor(j);
        TermList djy(Term::create1(dj,y));
        argTerms.push(djy);
        TermList xj(vars,false);
        varTerms.push(xj);
        if(con->argSort(j) == ta_sort){
          taTerms.push(djy);
          ta_vars.push(vars);
        }
        vars++;
      }
      // create y = con1(...d1(y)...d2(y)...)
      TermList coni(Term::create(con->functor(),(unsigned)argTerms.size(), argTerms.begin()));
      Literal* kneq = Literal::createEquality(true,y,coni,ta_sort);

      // create smaller(cons(x1,..,xn))
      Formula* smaller_coni = new AtomicFormula(Literal::create1(sty,true,
                                TermList(Term::create(con->functor(),(unsigned)varTerms.size(),varTerms.begin()))));

      FormulaList* smallers = FormulaList::empty();
      Stack<unsigned>::Iterator vtit(ta_vars);
      while(vtit.hasNext()){
        FormulaList::push(new AtomicFormula(Literal::create1(sty,true,TermList(vtit.next(),false))),smallers);
      }
      ASS(smallers);
      Formula* ax = Formula::quantify(new BinaryFormula(Connective::IMP,smaller_coni,
                      JunctionFormula::generalJunction(Connective::AND,smallers)));

      // now create a conjunction of smaller(d(y)) for each d
      FormulaList* And = FormulaList::empty(); 
      Stack<TermList>::Iterator tit(taTerms);
      while(tit.hasNext()){
        Formula* f = new AtomicFormula(Literal::create1(sty,true,tit.next()));
        FormulaList::push(f,And);
      }
      ASS(And);
      Formula* imp = new BinaryFormula(Connective::IMP,
                            new AtomicFormula(kneq),
                            JunctionFormula::generalJunction(Connective::AND,And));

      FormulaList::push(imp,conjunction);
      FormulaList::push(ax,conjunction);
    } 
  }
  // now !z : smallerThanY(z) => ~L[z]
  Formula* smallerImpNL = Formula::quantify(new BinaryFormula(Connective::IMP, 
                            new AtomicFormula(Literal::create1(sty,true,z)),
                            new AtomicFormula(replaceTermAndSquashSkolemsInLiteral(clit,term,z,vars))));

  FormulaList::push(smallerImpNL,conjunction);
  // quantify with mainVars explicitly
  Formula* exists = new QuantifiedFormula(Connective::EXISTS, mainVars,SList::empty(),
                       new JunctionFormula(Connective::AND,conjunction));

  Literal* conclusion = replaceTermAndSquashSkolemsInLiteral(clit,term,x,vars);
  FormulaList* orf = FormulaList::cons(exists,FormulaList::singleton(Formula::quantify(new AtomicFormula(conclusion))));
  Formula* hypothesis = new JunctionFormula(Connective::OR,orf);

  static ResultSubstitutionSP identity = ResultSubstitutionSP(new IdentitySubstitution());
  pair<Literal*, SLQueryResult> toResolve(conclusion, SLQueryResult(origLit, premise, identity));
  produceClauses(premise, origLit, hypothesis, rule, toResolve);
}

bool InductionClauseIterator::notDone(Literal* lit, Term* term)
{
  CALL("InductionClauseIterator::notDone");

  static DHSet<Literal*> done;
  static LiteralSubstitutionTree lis(env.options->unificationWithAbstraction(), false);
  static DHMap<TermList,TermList> blanks;
  const bool strengthenHyp = _opt.inductionStrengthenHypothesis();
  TermList srt = env.signature->getFunction(term->functor())->fnType()->result();

  if(!blanks.find(srt)){
    unsigned fresh = env.signature->addFreshFunction(0,"blank");
    env.signature->getFunction(fresh)->setType(OperatorType::getConstantsType(srt));
    TermList blank = TermList(Term::createConstant(fresh));
    blanks.insert(srt,blank);
  }

  unsigned var = 0;
  Literal* rep = replaceTermAndSquashSkolemsInLiteral(lit,term,blanks.get(srt),var);
  // If we strengthen the literal there might be an arbitrary number of
  // induction terms apart from the main one, so it is easier to replace
  // the rest with variables and check for variants in an index.
  // Otherwise there is only one term to replace and it gives a unique
  // literal, so a pointer check is sufficient.
  if (strengthenHyp) {
    if (lis.getVariants(rep, false, false).hasNext()) {
      return false;
    }

    lis.insert(rep, nullptr);
  } else {
    if(done.contains(rep)){
      return false;
    }

    done.insert(rep);
  }

  return true;
}

// Note: only works for unit clauses.
// TODO: encapsulate the 'done' map in a helper class to have it deallocate correctly.
bool InductionClauseIterator::notDoneInt(Literal* lit, Term* t, bool increasing, Term* bound1, Term* optionalBound2, bool fromComparison)
{
  CALL("InductionClauseIterator::notDoneInt");

  // Map structure:
  // (induction lit/t representation, increasing) -> ((bound1, optionalBound2) -> (existsFromComparisonTrue, {(induction term, fromComparison)}))
  static DHMap<pair<Literal*, bool>, DHMap<pair<Term*, Term*>, pair<bool, DHMap<Term*, bool>*>>*> done;

  // Create representation of lit/t combination
  static Term* blank;
  static unsigned freshInt = env.signature->addFreshFunction(0, "blank");
  if (!blank) {
    env.signature->getFunction(freshInt)->setType(OperatorType::getConstantsType(AtomicSort::intSort()));
    blank = Term::createConstant(freshInt);
  }
  Literal* rep = replaceTermInLiteral(lit,t,TermList(blank));

  auto key = make_pair(rep, increasing);
  DHMap<pair<Term*, Term*>, pair<bool, DHMap<Term*, bool>*>>* val;
  pair<bool, DHMap<Term*, bool>*>* p;
  auto bounds = make_pair(bound1, optionalBound2);
  if (done.find(key, val)) {
    // Check two conditions under which we can skip this induction literal/term/bounds combination:
    p = val->findPtr(bounds);
    if (p != nullptr) {
      // 1. either induction was applied on the same induction literal representation with the same bound(s),
      //    and the bound(s) came from comparison (i.e., its comparison with induction term was resolved away).
      if (p->first) return false;
      // 2. or induction was applied on the same induction literal & induction term with the same bound(s),
      //    and either now the bound did not come from comparison, or then it did.
      bool previousFromComparison = false;
      if (p->second->find(t, previousFromComparison) && (!fromComparison || previousFromComparison)) return false;
    }
    // There is a 3rd possibility: the bound now is an interpreted constant, and induction was applied
    // on the same induction lit and some other interpreted constant bound, which came from comparison,
    // and the bound then was <= this bound (if increasing) or >= this bound (if not increasing).
    // TODO: explore if it is worth it to implement this condition.
  }
  else {
    val = new DHMap<pair<Term*, Term*>, pair<bool, DHMap<Term*, bool>*>>();
    done.insert(key, val);
  }
  p = val->findPtr(bounds);
  DHMap<Term*, bool>* insideMap;
  if (p != nullptr) {
    insideMap = p->second;
    p->first |= fromComparison;
  } else {
    insideMap = new DHMap<Term*, bool>();
    val->insert(bounds, make_pair(fromComparison, insideMap));
  }
  bool previousFromComparison = false;
  if (!insideMap->find(t, previousFromComparison) || (!previousFromComparison && fromComparison)) {
    insideMap->set(t, fromComparison);
  }

  return true;
}

Term* InductionClauseIterator::getPlaceholderForTerm(const Term* t) {
  CALL("InductionClauseIterator::getPlaceholderForTerm");

  OperatorType* ot = env.signature->getFunction(t->functor())->fnType();
  bool added; 
  unsigned placeholderConstNumber = env.signature->addFunction("placeholder_" + ot->toString(), 0, added);
  if (added) {
    env.signature->getFunction(placeholderConstNumber)->setType(OperatorType::getConstantsType(ot->result()));
  }
  return Term::createConstant(placeholderConstNumber);
}

}
