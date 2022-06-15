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
 * @file Superposition.cpp
 * Defines class Superposition
 *
 */

#include "Superposition.hpp"
#include "Saturation/SaturationAlgorithm.hpp"
#include "Shell/Statistics.hpp"
#include "Kernel/EqHelper.hpp"

#define DEBUG(...) DBG(__VA_ARGS__)

namespace Inferences {
namespace IRC {

void Superposition::attach(SaturationAlgorithm* salg) 
{ 
  CALL("Superposition::attach");
  ASS(!_rhs);
  ASS(!_lhs);

  GeneratingInferenceEngine::attach(salg);

  _lhs=static_cast<decltype(_lhs)> (_salg->getIndexManager()
      ->request(IRC_SUPERPOSITION_LHS_SUBST_TREE) );
  _lhs->setShared(_shared);

  _rhs=static_cast<decltype(_rhs)>(_salg->getIndexManager()
      ->request(IRC_SUPERPOSITION_RHS_SUBST_TREE));
  _rhs->setShared(_shared);

}

void Superposition::detach() 
{
  CALL("Superposition::detach");
  ASS(_salg);

  _lhs=0;
  _salg->getIndexManager()->release(IRC_SUPERPOSITION_LHS_SUBST_TREE);
  _rhs=0;
  _salg->getIndexManager()->release(IRC_SUPERPOSITION_RHS_SUBST_TREE);
  GeneratingInferenceEngine::detach();
}
  

#if VDEBUG
void Superposition::setTestIndices(Stack<Indexing::Index*> const& indices) 
{
  _lhs = (decltype(_lhs)) indices[0]; 
  _lhs->setShared(_shared);
  _rhs = (decltype(_rhs)) indices[1]; 
  _rhs->setShared(_shared);
}
#endif

// C1 \/ s1 ≈ t             C2 \/ L[s2]
// ====================================
//   (C1 \/ C2 \/ L[t])σ \/ Cnst
// where
// • uwa(s1,s2)=⟨σ,Cnst⟩
// • (s1 ≈ t)σ /⪯ C1σ
// •    L[s2]σ  ∈ Lit+ and L[s2]σ /⪯ C2σ
//   or L[s2]σ /∈ Lit+ and L[s2]σ /≺ C2σ
// • s2σ ⊴ x ∈ active(L[s2]σ)
// • s1σ /⪯ tσ
// • s1 is not a variable
// • s2 is not a variable
Option<Clause*> Superposition::applyRule(
    Lhs const& lhs, unsigned lhsVarBank,
    Rhs const& rhs, unsigned rhsVarBank,
    UwaResult& uwa
    ) const 
{
  CALL("Superposition::applyRule(Lhs const&, unsigned, Rhs const&, unsigned, UwaResult&)")
  MeasureTime time(env.statistics->ircSup);

  ASS (lhs.literal()->isEquality() && lhs.literal()->isPositive())
  auto s1 = lhs.biggerSide();
  auto s2 = rhs.toRewrite();
  auto nothing = [&]() {
    time.applicationCancelled();
    return Option<Clause*>();
  };
  ASS(!(s1.isVar() && lhs.isFracNum()))
  ASS(!s2.isVar())

#define check_side_condition(cond, cond_code)                                                       \
    if (!(cond_code)) {                                                                             \
      DEBUG("side condition not fulfiled: ", cond)                                                  \
      return nothing();                                                                             \
    }                                                                                               \



  Stack<Literal*> concl(lhs.clause()->size() - 1 // <- C1σ
                      + rhs.clause()->size() - 1 // <- C2σ
                      + 1                        // <- L[s2]σ 
                      + uwa.cnst().size());      // <- Cnstσ


  auto unifySorts = [](auto s1, auto s2) -> Option<TermList> {
    static RobSubstitution subst;
    if (!subst.unify(s1, 0, s2, 0)) {
      return Option<TermList>();
    } else {
      ASS_EQ(subst.apply(s1,0), subst.apply(s2,0))
      return Option<TermList>(subst.apply(s1, 0));
    }
  };

  check_side_condition(
      "s1 and s2 are of unifyable sorts", 
      unifySorts(
        SortHelper::getEqualityArgumentSort(lhs.literal()), 
        SortHelper::getResultSort(s2.term())
        ).isSome()
      )

  auto L1σ = uwa.sigma(lhs.literal(), lhsVarBank);
  check_side_condition(
        "(s1 ≈ t)σ /⪯ C1σ",
        lhs.contextLiterals()
           .all([&](auto L) {
             auto Lσ = uwa.sigma(L, lhsVarBank);
             concl.push(Lσ);
             return OrderingUtils2::notLeq(_shared->ordering->compare(L1σ, Lσ));
           }))

  // •    L[s2]σ  ∈ Lit+ and L[s2]σ /⪯ C2σ
  //   or L[s2]σ /∈ Lit+ and L[s2]σ /≺ C2σ
  auto L2σ = uwa.sigma(rhs.literal(), rhsVarBank);
  bool inLitPlus = rhs.inLitPlus();
  check_side_condition(
      inLitPlus ? "L[s2]σ /⪯ C2σ"
                : "L[s2]σ /≺ C2σ",
        rhs.contextLiterals()
           .all([&](auto L) {
             auto Lσ = uwa.sigma(L, rhsVarBank);
             concl.push(Lσ);
             return inLitPlus ? OrderingUtils2::notLeq(_shared->ordering->compare(L2σ, Lσ))
                              : OrderingUtils2::notLess(_shared->ordering->compare(L2σ, Lσ));
           }));

  auto s2σ = uwa.sigma(s2, rhsVarBank);

  check_side_condition(
      "s2σ ⊴ ti ∈ active(L[s2]σ)", 
      _shared->activePositions(L2σ)
        .any([&](auto ti) 
             { return _shared->subtermEq(s2σ, ti); }))

  check_side_condition(
      "L[s2]σ /⪯ L1σ", // TODO is this the correct thing? if so make sure we do that for fourrier motzkin and friends as well
      OrderingUtils2::notLeq(_shared->ordering->compare(L2σ, L1σ)))


  auto s1σ = uwa.sigma(lhs.biggerSide(), lhsVarBank);
  auto tσ  = uwa.sigma(lhs.smallerSide(), lhsVarBank);
  check_side_condition(
      "s1σ /⪯ tσ",
      OrderingUtils2::notLeq(_shared->ordering->compare(s1σ, tσ)))


  auto resolvent = EqHelper::replace(L2σ, s2σ, tσ);
  //   ^^^^^^^^^--> L[t]σ
  DEBUG("replacing: ", *L2σ, " [ ", s2σ, " -> ", tσ, " ] ==> ", *resolvent);
  concl.push(resolvent);

  // adding Cnst
  concl.loadFromIterator(uwa.cnstLiterals());

  Inference inf(GeneratingInference2(Kernel::InferenceRule::IRC_SUPERPOSITION, lhs.clause(), rhs.clause()));
  auto out = Clause::fromStack(concl, inf);
  DEBUG("out: ", *out);
  return Option<Clause*>(out);
}


ClauseIterator Superposition::generateClauses(Clause* premise) 
{
  CALL("InequalityResolution::generateClauses(Clause* premise)")
  ASS(_lhs)
  ASS(_rhs)
  ASS(_shared)
  // TODO get rid of stack and unify with InequalityResolution
  Stack<Clause*> out;

  for (auto const& lhs : Lhs::iter(*_shared, premise)) {
    DEBUG("lhs: ", lhs)
    for (auto rhs_sigma : _rhs->find(lhs.key())) {
      auto& rhs = *std::get<0>(rhs_sigma);
      auto& sigma = std::get<1>(rhs_sigma);
      DEBUG("  rhs: ", rhs)
      auto res = applyRule(lhs, 0, rhs, 1, sigma);
      DEBUG("")
      if (res.isSome()) {
        out.push(res.unwrap());
      }
    }
  }

  for (auto const& rhs : Rhs::iter(*_shared, premise)) {
    DEBUG("rhs: ", rhs)
    for (auto lhs_sigma : _lhs->find(rhs.key())) {
      auto& lhs = *std::get<0>(lhs_sigma);
      auto& sigma = std::get<1>(lhs_sigma);
      DEBUG("  lhs: ", lhs)
      auto res = applyRule(lhs, 1, rhs, 0, sigma);
      DEBUG("")
      if (res.isSome()) {
        out.push(res.unwrap());
      }
    }
  }
  return pvi(ownedArrayishIterator(std::move(out)));
}

// TODO move to appropriate place

SimplifyingGeneratingInference::ClauseGenerationResult InequalityTautologyDetection::generateSimplify(Clause* premise) {
  Map<AnyIrcLiteral, bool, StlHash> lits;
    
  for (auto lit : iterTraits(premise->iterLits())) {
    auto norm_ = _shared->renormalize(lit);
    if (norm_.isSome()) {
      auto norm = norm_.unwrap();
      lits.insert(norm, true);
      auto opposite = norm.apply([&](auto lit) { return AnyIrcLiteral(lit.negation()); });
      if (lits.find(opposite)) {
        // std::cout << "bla" << std::endl;
        return ClauseGenerationResult {
          .clauses = ClauseIterator::getEmpty(),
          .premiseRedundant = true,
        };
      }
    }
  }

  return ClauseGenerationResult {
      .clauses = ClauseIterator::getEmpty(),
      .premiseRedundant = false,
    };
}


} // namespace IRC 
} // namespace Inferences 
