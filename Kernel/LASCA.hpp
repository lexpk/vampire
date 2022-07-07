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
 * @file LASCA.cpp
 * Defines all functionality shared among the components of the inequality resolution calculus.
 *
 */



#ifndef __LASCA__
#define __LASCA__

#include "Kernel/Formula.hpp"
#include "Lib/Int.hpp"
#include "Forwards.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Indexing/ResultSubstitution.hpp"

#include "Signature.hpp" 
#include "SortHelper.hpp"
#include "TermIterators.hpp"
#include "Term.hpp"
#include "Theory.hpp"
#include "NumTraits.hpp"
#include "Debug/Tracer.hpp"
#include "Lib/Coproduct.hpp"
#include <algorithm>
#include <utility>
#include <type_traits>
#include <functional>
#include "Lib/Hash.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Option.hpp"
#include "Debug/Tracer.hpp"
#include "Kernel/Polynomial.hpp"
#include "Kernel/BottomUpEvaluation.hpp"
#include "Kernel/BottomUpEvaluation/TermList.hpp"
#include "Kernel/BottomUpEvaluation/PolyNf.hpp"
#include "Inferences/InferenceEngine.hpp"
#include "Inferences/PolynomialEvaluation.hpp"
#include "Kernel/PolynomialNormalizer.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/OrderingUtils.hpp"
#define DEBUG(...) //DBG(__VA_ARGS__)



namespace Kernel {
  using Inferences::PolynomialEvaluation;

  template<class A>
  struct Indexed {
    unsigned idx;
    A self;
    A& operator*() { return self; }
    A const& operator*() const { return self; }
    A* operator->() { return &self; }
  };
   

  template<class A>
  Indexed<A> indexed(unsigned idx, A self) 
  { return {.idx = idx, .self = std::move(self), }; }

  enum class LascaPredicate {
    EQ,
    NEQ,
    GREATER,
    GREATER_EQ,
  };

  template<class NumTraits>
  Literal* LascaPredicateCreateLiteral(LascaPredicate p, TermList t)
  { 
    switch(p) {
      case LascaPredicate::EQ: return Literal::createEquality(true, t, NumTraits::zero(), NumTraits::sort());
      case LascaPredicate::NEQ: return Literal::createEquality(false, t, NumTraits::zero(), NumTraits::sort());
      case LascaPredicate::GREATER_EQ: return NumTraits::geq(true, t, NumTraits::zero());
      case LascaPredicate::GREATER: return NumTraits::greater(true, t, NumTraits::zero());
    }
    ASSERTION_VIOLATION
  }

  /** returns true iff the predicate is > or >= */
  bool isInequality(LascaPredicate const& self);

  std::ostream& operator<<(std::ostream& out, LascaPredicate const& self);

  /** 
   * Represents an inequality literal normalized for the rule InequalityResolution.
   * this means it is a literal of the form
   *      term == 0 or term != 0 or term >= 0 or term > 0 (for Reals and Rationals)
   * or   term == 0 or term != 0              or term > 0 (for Integers)
   */
  template<class NumTraits_>
  class LascaLiteral {
  public:
    using NumTraits = NumTraits_;
    using Numeral = typename NumTraits_::ConstantType;
  private:
    Perfect<Polynom<NumTraits>> _term;
    LascaPredicate _symbol;
    friend struct std::hash<LascaLiteral>;

  public:

    LascaLiteral(Perfect<Polynom<NumTraits>> term, LascaPredicate symbol) 
      : _term(term), _symbol(symbol) 
    { _term->integrity(); }

    friend class InequalityNormalizer;

    /* returns the lhs of the inequality lhs >= 0 (or lhs > 0) */
    Polynom<NumTraits> const& term() const
    { return *_term; }

    LascaPredicate symbol() const
    { return _symbol; }

    friend std::ostream& operator<<(std::ostream& out, LascaLiteral const& self) 
    { return out << self._term << " " << self._symbol << " 0"; }

    LascaLiteral negation() const
    {
      // TODO  handle that actually -t == 0 and t == 0 are equivalent
      return LascaLiteral(perfect(-(*_term)), [&](){
            switch(_symbol) {
            case LascaPredicate::EQ:  return LascaPredicate::NEQ;
            case LascaPredicate::NEQ: return LascaPredicate::EQ;
            case LascaPredicate::GREATER: return LascaPredicate::GREATER_EQ;
            case LascaPredicate::GREATER_EQ: return LascaPredicate::GREATER;
            }
            ASSERTION_VIOLATION
          }());
    }

    Literal* denormalize() const
    {
      auto l = term().denormalize();
      auto r = NumTraits::zero();
      switch(symbol()) {
        case LascaPredicate::EQ:  return NumTraits::eq(true, l, r);
        case LascaPredicate::NEQ: return NumTraits::eq(false, l, r);
        case LascaPredicate::GREATER: return NumTraits::greater(true, l, r);
        case LascaPredicate::GREATER_EQ: return NumTraits::geq(true, l, r);
      }
      ASSERTION_VIOLATION
    }

    bool isInequality() const
    { return Kernel::isInequality(symbol()); }

    friend bool operator==(LascaLiteral const& lhs, LascaLiteral const& rhs)
    { return std::tie(lhs._symbol, lhs._term) ==  std::tie(rhs._symbol, rhs._term); }
  };


  using AnyConstantType = Coproduct< IntegerConstantType
                                   , RationalConstantType
                                   , RealConstantType
                                   >;

  using AnyLascaLiteral = Coproduct< LascaLiteral< IntTraits>
                                 , LascaLiteral< RatTraits>
                                 , LascaLiteral<RealTraits>
                                 >;

  /** 
   * Represents an inequality literal normalized for the rule InequalityResolution.
   * this means it is a literal of the form
   *      term > 0 or term >= 0 (for Reals and Rationals)
   * or   term > 0              (for Integers)
   */
  template<class NumTraits>
  class InequalityLiteral {
    LascaLiteral<NumTraits> _self;

  public:
    InequalityLiteral(Perfect<Polynom<NumTraits>> term, bool strict) 
      : InequalityLiteral(LascaLiteral<NumTraits>(term, strict ? LascaPredicate::GREATER : LascaPredicate::GREATER_EQ))
    {}

    LascaLiteral<NumTraits> const& inner() const { return _self; }

    explicit InequalityLiteral(LascaLiteral<NumTraits> self) 
      : _self(std::move(self)) 
    { ASS(self.isInequality()) }

    /* returns the lhs of the inequality lhs >= 0 (or lhs > 0) */
    Polynom<NumTraits> const& term() const
    { return _self.term(); }

    /* 
     * returns whether this is a strict inequality (i.e. >), 
     * or a non-strict one (i.e. >=) 
     * */
    bool strict() const
    { return _self.symbol() == LascaPredicate::GREATER; }

    friend std::ostream& operator<<(std::ostream& out, InequalityLiteral const& self) 
    { return out << self._self; }

    Literal* denormalize() const
    { return _self.denormalize(); }
  };

  using AnyInequalityLiteral = Coproduct< InequalityLiteral< IntTraits>
                                        , InequalityLiteral< RatTraits>
                                        , InequalityLiteral<RealTraits>
                                        >;

  template<class NumTraits>
  Option<InequalityLiteral<NumTraits>> inequalityLiteral(LascaLiteral<NumTraits> lit) 
  {
    return lit.isInequality() ? some(InequalityLiteral<NumTraits>(lit)) 
                              : Option<InequalityLiteral<NumTraits>>();
  }

  class InequalityNormalizer {
    // Map<Literal*, Option<InequalityLiteral>> _normalized;
    PolynomialEvaluation _eval;
    const bool _strong;

  public:
    PolynomialEvaluation& evaluator() { return _eval; }
    PolynomialEvaluation const& evaluator() const { return _eval; }

    /** param strong enables rewrites 
     * t >= 0 ==> t > 0 \/ t == 0
     * t != 0 ==> t > 0 \/ -t > 0
     */
    InequalityNormalizer(bool strong) 
      : _eval(/* removeZero */ false)
      , _strong(strong) {  }

    template<class NumTraits> Option<MaybeOverflow<Stack<LascaLiteral<NumTraits>>>> normalizeLasca(Literal* lit) const;
    template<class NumTraits> Option<MaybeOverflow<LascaLiteral<NumTraits>>> renormalizeLasca(Literal* lit) const;

    Option<MaybeOverflow<AnyLascaLiteral>> renormalize(Literal* lit) const;

    template<class NumTraits> Option<MaybeOverflow<InequalityLiteral<NumTraits>>> renormalizeIneq(Literal* lit) const;

    // Literal* renormalizeLiteral(Literal* lit) const;
    Stack<Literal*> normalizeLiteral(Literal* lit) const;
    bool isNormalized(Clause* cl)  const;
  private: 
    Literal* normalizeUninterpreted(Literal* lit) const;
  };

  struct LascaState;
  using UwaSubstitution = Coproduct<RobSubstitution, Indexing::ResultSubstitutionSP>; 

  template<class TermOrLit> 
  auto applySubst(Indexing::ResultSubstitution& subst, TermOrLit t, int varBank) { return subst.applyTo(t, varBank);  }

  template<class TermOrLit> 
  auto applySubst(Indexing::ResultSubstitutionSP const& subst, TermOrLit t, int varBank) { return subst->applyTo(t, varBank);  }

  template<class TermOrLit> 
  auto applySubst(RobSubstitution const& subst, TermOrLit t, int varBank) { return subst.apply(t, varBank);  }

  template<class TermOrLit> 
  auto applySubst(UwaSubstitution const& subst, TermOrLit t, int varBank)
  { return subst.apply([&](auto& s) { return applySubst(s, t, varBank); });  }


  struct UwaResult {
    UwaSubstitution _sigma;
    Stack<UnificationConstraint> _cnst;

    UwaResult(RobSubstitution sigma, Stack<UnificationConstraint> cnst) 
      : _sigma(decltype(_sigma)(std::move(sigma)))
      , _cnst(std::move(cnst)) 
    {  }

    template<class T>
    UwaResult(Indexing::TermQueryResult<T> const& qr)
      : _sigma(decltype(_sigma)(qr.substitution))
      , _cnst( qr.constraints ? *qr.constraints : decltype(_cnst)() )
    { }

    UwaResult(UwaResult&&) = default;
    UwaResult& operator=(UwaResult&&) = default;

    template<class Subst>
    static auto cnstLiterals(Subst& sigma, Stack<UnificationConstraint> const& cnst)
    {
      return iterTraits(cnst.iterFifo())
        .map([&](auto c){
          auto toTerm = [&](pair<TermList, unsigned> & constraintPair) -> TermList
                        { return applySubst(sigma, constraintPair.first, constraintPair.second); };
          auto sort = SortHelper::getResultSort(c.first.first.term());
          // lσ != rσ
          return Literal::createEquality(false, toTerm(c.first), toTerm(c.second), sort);
        });
    }

    auto const& cnst() const { return _cnst; }

    template<class TermOrLit>
    auto sigma(TermOrLit x, unsigned varBank) const 
    { return applySubst(_sigma, x, varBank); }

    auto cnstLiterals() const
    { return cnstLiterals(_sigma, _cnst); }

    friend std::ostream& operator<<(std::ostream& out, UwaResult const& self)
    { 
      out << "⟨" << self._sigma << ", [";
      auto iter = self.cnstLiterals();
      if (iter.hasNext()) {
        out << *iter.next();
        while (iter.hasNext())
          out << " \\/ " << *iter.next();
      }
      return out << "]⟩"; 
    }
  private:
    // UwaResult() : _sigma(), _cnst() {  }
    friend struct LascaState;
  };

  template<class NumTraits>
  struct SelectedAtomicTerm 
  {
    unsigned litIdx;
    Literal* literal;
    LascaLiteral<NumTraits> ircLit;
    unsigned termIdx;
    Monom<NumTraits> self;

    friend std::ostream& operator<<(std::ostream& out, SelectedAtomicTerm const& self)
    { return out << self.self << " @ " << *self.literal; }
  };

  struct SelectedLiteral {
    Clause* cl;
    unsigned litIdx;
    Option<AnyLascaLiteral> interpreted;

    SelectedLiteral(Clause* cl, unsigned litIdx, LascaState& shared);

    Literal* literal() const { return (*cl)[litIdx]; }
    Clause* clause() const { return cl; }


    auto contextLiterals() const
    { return range(0, clause()->size())
              .filter([&](auto i) { return i != litIdx; }) 
              .map([&](auto i) { return (*clause())[i]; }); }
              
    auto asTuple() const
    { return std::make_tuple(cl->number(), litIdx); }

    IMPL_COMPARISONS_FROM_TUPLE(SelectedLiteral)
  };


  class SelectedUninterpretedEquality : public SelectedLiteral
  {
    unsigned _term;
   public:
    SelectedUninterpretedEquality(SelectedLiteral lit, unsigned term) 
      : SelectedLiteral(std::move(lit))
      , _term(term)
    { 
      ASS(interpreted.isNone())
      ASS(literal()->isEquality())
      ASS(_term <= 1)
    }

    TermList biggerSide() const
    { return literal()->termArg(_term); }

    TermList smallerSide() const
    { return literal()->termArg(1 - _term); }

    auto asTuple() const { return std::tie(_term, (SelectedLiteral const&) *this); }
    IMPL_COMPARISONS_FROM_TUPLE(SelectedUninterpretedEquality)
  };

  class SelectedSummand : public SelectedLiteral
  {
    unsigned _term;
  public:

    SelectedSummand(
      SelectedLiteral lit,
      unsigned term
    ) : SelectedLiteral(std::move(lit))
      , _term(term) 
    {
      ASS(interpreted.isSome())
    }

    auto termIdx() const { return _term; }

    // explicit SelectedSummand(SelectedSummand const&) = default;
    // SelectedSummand(SelectedSummand&&) = default;
    // SelectedSummand& operator=(SelectedSummand&&) = default;

    auto numeral() const 
    { return ircLiteral()
          .apply([this](auto& lit) 
              { return AnyConstantType(lit.term().summandAt(_term).numeral); }); }

    template<class NumTraits>
    auto numeral() const 
    { return numeral().unwrap<typename NumTraits::ConstantType>(); }

    auto nContextTerms() const 
    { return ircLiteral().apply([](auto& lit) { return lit.term().nSummands() - 1; }); }

    AnyLascaLiteral const& ircLiteral() const
    { return interpreted.unwrap(); }

    template<class NumTraits>
    auto const& ircLiteral() const
    { return ircLiteral().template unwrap<LascaLiteral<NumTraits>>(); }

    template<class NumTraits>
    auto contextTerms() const 
    { 
      auto& lit = ircLiteral<NumTraits>();
      return range(0, lit.term().nSummands()) 
                .filter([&](unsigned i) { return i != _term; })
                .map([&](unsigned i) { return lit.term().summandAt(i); });
    }

    bool isInequality() const
    { return ircLiteral().apply([](auto& lit)
                               { return lit.isInequality(); }); }

    auto monom() const 
    { return ircLiteral()
          .apply([this](auto& lit) 
              { return lit.term().summandAt(_term).factors->denormalize(); }); }

    auto sign() const 
    { return numeral().apply([](auto const& self) { return self.sign(); }); }

    auto numTraits() const 
    { return numeral().apply([](auto n) 
        { return Coproduct<IntTraits, RatTraits, RealTraits>(NumTraits<decltype(n)>{}); });
    }

    TermList sort() const { return numTraits().apply([](auto num) { return num.sort(); });  }

    auto symbol() const
    { return ircLiteral().apply([](auto& l) { return l.symbol(); }); }

    using Key = TermList;
    auto key() const { return monom(); }
    friend std::ostream& operator<<(std::ostream& out, SelectedSummand const& self);

    auto asTuple() const
    { return std::tie(_term, (SelectedLiteral const&)*this); }

    IMPL_COMPARISONS_FROM_TUPLE(SelectedSummand)
  };

  class SelectedIntegerEquality : public SelectedSummand 
  {
  public:
    SelectedIntegerEquality(SelectedSummand s) 
      : SelectedSummand(std::move(s)) 
    { ASS(numTraits() == decltype(numTraits())(IntTraits{})) }

    TermList biggerSide() const 
    { return IntTraits::mulSimpl(numeral<IntTraits>(), monom()); }

    TermList smallerSide() const 
    { return IntTraits::sum(contextTerms<IntTraits>().map([](auto t) { return (-t).denormalize(); })); }

    // friend std::ostream& operator<<(std::ostream& out, SelectedIntegerEquality const& self)
    // { return out << (SelectedSummand const&)self; }

  };

  class SelectedEquality 
  {
    Coproduct<SelectedSummand, SelectedIntegerEquality, SelectedUninterpretedEquality>  _inner;

  public:

    explicit SelectedEquality(SelectedSummand s) 
      : _inner(decltype(_inner)::variant<0>(std::move(s))) 
    { 
      ASS(!_inner.unwrap<0>().isInequality()) 
      ASS(_inner.unwrap<0>().numTraits().apply([](auto x) { return x.isFractional(); }))
    }


    explicit SelectedEquality(SelectedIntegerEquality s) 
      : _inner(decltype(_inner)::variant<1>(std::move(s))) 
    { 
    }

    explicit SelectedEquality(SelectedUninterpretedEquality s) 
      : _inner(decltype(_inner)(std::move(s))) {}

    Clause* clause() const 
    { return _inner.apply([](auto& x) { return x.clause(); }); }

    unsigned litIdx() const 
    { return _inner.apply([](auto& x) { return x.litIdx; }); }

    bool positive() const 
    { return literal()->isPositive(); }

    bool isFracNum() const
    { 
      ASS(!_inner.template is<SelectedSummand>() 
        || _inner.template unwrap<SelectedSummand>().numTraits().apply([](auto x) { return x.isFractional(); }))
      return _inner.template is<SelectedSummand>(); 
    }

    TermList biggerSide() const 
    { return _inner.match(
        [](SelectedSummand               const& x) { return x.monom(); },
        [](SelectedIntegerEquality       const& x) { return x.biggerSide(); },
        [](SelectedUninterpretedEquality const& x) { return x.biggerSide(); }); }

    TermList smallerSide() const 
    { return _inner.match(
        [&](SelectedSummand               const& sel) 
        { return sel.numTraits().apply([&](auto numTraits) {
            return ifIntTraits(numTraits,
                [](IntTraits) -> TermList { ASSERTION_VIOLATION },
                [&](auto numTraits) {
                   using NumTraits = decltype(numTraits);
                   auto k = sel.numeral<NumTraits>();
                   return NumTraits::sum(sel.contextTerms<NumTraits>()
                        .map([&](auto monom) { return (monom / (-k)).denormalize();  }));
                });
            });
        },
        [](SelectedIntegerEquality       const& x) { return x.smallerSide(); },
        [](SelectedUninterpretedEquality const& x) { return x.smallerSide(); }); }

    auto contextLiterals() const
    { return _inner.apply([](auto& x) { return x.contextLiterals(); }); }
    // { return ifElseIter(
    //     _inner.is<0>(), 
    //     [&]() { return _inner.unwrap<0>().contextLiterals(); },
    //     // else
    //     [&]() { return _inner.unwrap<1>().contextLiterals(); }); }

    TermList key() const 
    { return biggerSide(); }

    Literal* literal() const
    { return _inner.apply([](auto& x) { return x.literal(); }); }

    TermList sort() const { ASSERTION_VIOLATION  }

    friend std::ostream& operator<<(std::ostream& out, SelectedEquality const& self)
    { 
      out << self.biggerSide() << (self.positive() ? " = " : " != ") << self.smallerSide();
      for (auto l : self.contextLiterals()) {
        out << " \\/ " << *l;
      }
      return out; 
    }

    auto asTuple() const { return std::tie(_inner); }
    IMPL_COMPARISONS_FROM_TUPLE(SelectedEquality)
  };
  class SelectedUninterpretedPredicate : public SelectedLiteral {
  public:
    SelectedUninterpretedPredicate(SelectedLiteral lit)
      : SelectedLiteral(std::move(lit))
    { 
      ASS(interpreted.isNone())
      ASS(!literal()->isEquality())
    }
  };
  using SelectionCriterion = OrderingUtils2::SelectionCriterion;

  struct LascaState 
  {
    CLASS_NAME(LascaState);
    USE_ALLOCATOR(LascaState);

    // TODO get rid of this
    static std::shared_ptr<LascaState> globalState;

  private:
    LascaState(
          InequalityNormalizer normalizer,
          Ordering* const ordering,
          Shell::Options::UnificationWithAbstraction const uwa
        )
      : normalizer(std::move(normalizer))
      , ordering(std::move(ordering))
      , uwa(std::move(uwa)) {}

  public:
    InequalityNormalizer normalizer;
    Ordering* const ordering;
    Shell::Options::UnificationWithAbstraction const uwa;

    static std::shared_ptr<LascaState> create(
          InequalityNormalizer normalizer,
          Ordering* const ordering,
          Shell::Options::UnificationWithAbstraction const uwa
        ) 
    {
      globalState = make_shared(LascaState(std::move(normalizer), ordering, uwa));
      return globalState;
    }

    bool equivalent(TypedTermList lhs, TypedTermList rhs) 
     { return normalize(lhs) == normalize(rhs); }

    auto maxLits(Clause* cl, SelectionCriterion sel) {
      CALL("LascaState::maxLits")
      return OrderingUtils2::maxElems(
          cl->size(), 
          [=](unsigned l, unsigned r) 
          { return ordering->compare((*cl)[l], (*cl)[r]); },
          sel)
        .map([=](auto i) 
            { return SelectedLiteral(cl, i, *this); });
    }

    template<class LitOrTerm>
    bool notLess(LitOrTerm lhs, LitOrTerm rhs)
    { return OrderingUtils2::notLess(ordering->compare(lhs, rhs)); }

    template<class LitOrTerm>
    bool notLeq(LitOrTerm lhs, LitOrTerm rhs)
    { return OrderingUtils2::notLeq(ordering->compare(lhs, rhs)); }

    template<class NumTraits>
    auto maxSummandIndices(LascaLiteral<NumTraits> const& lit, SelectionCriterion selection)
    {
        auto monomAt = [=](auto i) 
             { return lit.term().summandAt(i).factors->denormalize(); }; 

        return OrderingUtils2::maxElems(
                  lit.term().nSummands(),
                  [=](unsigned l, unsigned r) 
                  { return ordering->compare(monomAt(l), monomAt(r)); },
                  selection);
    }

    auto maxEqIndices(Literal* lit, SelectionCriterion sel)
    {
      Stack<unsigned> is(2);
      auto iter = [](Stack<unsigned> out)  
                  { return iterTraits(ownedArrayishIterator(std::move(out))); };
      switch (sel) {
        case SelectionCriterion::ANY:
          return iter({0,1});

        case SelectionCriterion::WEAKLY_MAX:
          switch (ordering->compare(lit->termArg(0), lit->termArg(1))) {
            case Ordering::Result::GREATER: return iter({0});
            case Ordering::Result::LESS:    return iter({1});

            case Ordering::Result::LESS_EQ:
            case Ordering::Result::GREATER_EQ:
            case Ordering::Result::EQUAL:
            case Ordering::Result::INCOMPARABLE: return iter({0, 1});
          }

        case SelectionCriterion::STRICTLY_MAX:
          switch (ordering->compare(lit->termArg(0), lit->termArg(1))) {
            case Ordering::Result::GREATER_EQ:
            case Ordering::Result::GREATER: return iter({0});
            case Ordering::Result::LESS_EQ:
            case Ordering::Result::LESS:    return iter({1});
            case Ordering::Result::EQUAL:        return iter(Stack<unsigned>());
            case Ordering::Result::INCOMPARABLE: return iter({0, 1});
          }
      }

      return iterTraits(ownedArrayishIterator(std::move(is)));
    }

    auto activePositions(Literal* l) -> IterTraits<VirtualIterator<TermList>>
    {
      return iterTraits(renormalize(l)
        .match(
          [=](AnyLascaLiteral l) -> VirtualIterator<TermList> {
            return std::move(l).apply([=](auto l) -> VirtualIterator<TermList> {
                return pvi(maxSummandIndices(l, SelectionCriterion::STRICTLY_MAX)
                         .map([=](auto i) {
                             return l.term().summandAt(i).factors->denormalize();
                         }));
            });
          },
          [=]() {
            if (l->isEquality()) {
              return pvi(maxEqIndices(l, SelectionCriterion::STRICTLY_MAX)
                .map([=](auto i) { return l->termArg(i); }));
            } else {
                return pvi(termArgIter(l));
            }
          }));
    }

    bool subtermEq(TermList sub, TermList sup) {
      // TODO add assertion that sub is an atomic term
      return normalizer.evaluator().evaluateToTerm(sup)
        .containsSubterm(normalizer.evaluator().evaluateToTerm(sub));
    }


    auto maxSummands(SelectedLiteral sel_lit , SelectionCriterion sel) 
    { return sel_lit.interpreted.unwrap()
                .apply([&](auto& lit) 
                       { return maxSummandIndices(lit, sel); })
                .map([=](auto i) 
                     { return SelectedSummand(sel_lit, i); }); }


    auto selectedActivePositions(
        Clause* cl, SelectionCriterion selLit, 
        SelectionCriterion selSum,
        bool includeUnshieldedNumberVariables)
    {
      using Out = Coproduct<SelectedSummand, SelectedUninterpretedEquality, SelectedUninterpretedPredicate>;
      return maxLits(cl, selLit)
        .flatMap([=](auto sel_lit) -> VirtualIterator<Out> {
            auto lit = sel_lit.literal();
            if (sel_lit.interpreted.isSome()) {
              return pvi(maxSummands(sel_lit, selSum)
                  .filter([=](auto x) { return includeUnshieldedNumberVariables || x.numTraits().apply([](auto x) { return !x.isFractional(); }) || !x.monom().isVar(); })
                  .map([](auto x) { return Out(std::move(x)); }));

            } else if (lit->isEquality()) {
              return pvi(maxEqIndices(lit, selSum)
                        .map([=](auto j) 
                            { return Out(SelectedUninterpretedEquality(sel_lit, j)); }));
            } else {
              return pvi(getSingletonIterator(Out(SelectedUninterpretedPredicate(sel_lit))));
            }
        });
    }

    auto selectedEqualities(Clause* cl, SelectionCriterion selLit, SelectionCriterion selTerm, bool includeUnshieldedNumberVariables) {
      using Out = SelectedEquality;
      return selectedActivePositions(cl, selLit, selTerm, includeUnshieldedNumberVariables)
        .filterMap([](auto x) -> Option<Out>
                   { return x.match(
                       [](SelectedSummand& x) {
                          return x.isInequality() ? Option<Out>()
                              : x.numTraits().template is<IntTraits>() ? Option<Out>(Out(SelectedIntegerEquality(std::move(x))))
                              : Option<Out>(Out(std::move(x)));
                       },

                       [](SelectedUninterpretedEquality& x) 
                       { return Option<Out>(Out(std::move(x))); },

                       [](SelectedUninterpretedPredicate&) 
                       { return Option<Out>(); });
        });
    }


    auto selectedSummands(Clause* cl, SelectionCriterion selLit, SelectionCriterion selTerm, bool includeUnshieldedNumberVariables) {
      using Out = SelectedSummand;
      return selectedActivePositions(cl, selLit, selTerm, includeUnshieldedNumberVariables)
        .filterMap([](auto x) -> Option<Out> {
            return x.match(
                 [](SelectedSummand& x) 
                 { return Option<Out>(std::move(x)); },

                 [](SelectedUninterpretedEquality&) 
                 { return Option<Out>(); },

                 [](SelectedUninterpretedPredicate&) 
                 { return Option<Out>(); });
        });
    }


    // template<class GetSummand> auto iterSelectedTerms(GetSummand getSummand, unsigned litSize, bool strict = false);
    // template<class NumTraits> Stack<Monom<NumTraits>> selectedTerms(LascaLiteral<NumTraits>const& lit, bool strict = false);
    // template<class NumTraits> Stack<SelectedAtomicTerm<NumTraits>> selectedTerms(Clause* cl, bool strictlyMaxLiterals = false, bool strictlyMaxTerms = false);

    // Stack<Literal*> selectedLiterals(Clause* cl, bool strictlyMax = false);
    // Stack<std::pair<Literal*, unsigned>> selectedLiteralsWithIdx(Clause* cl, bool strictlyMax = false);
    // Stack<Literal*> selectedLiterals(Stack<Literal*> cl, bool strictlyMax = false);
    // Stack<Literal*> strictlySelectedLiterals(Clause* cl) { return selectedLiterals(cl, true); }

  private:
    // Stack<Literal*> maxLiterals(Clause* cl, bool strictlyMax = false);
    // Stack<std::pair<Literal*, unsigned>> maxLiteralsWithIdx(Clause* cl, bool strictlyMax = false);
    // Stack<Literal*> maxLiterals(Stack<Literal*> cl, bool strictlyMax = false);
    // Stack<Literal*> strictlyMaxLiterals(Clause* cl) { return maxLiterals(cl, true); }

  public:

    Option<UwaResult> unify(TermList lhs, TermList rhs) const;
    Option<AnyLascaLiteral> renormalize(Literal*);
    Option<AnyInequalityLiteral> renormalizeIneq(Literal*);
    PolyNf normalize(TypedTermList);

    template<class LitOrTerm, class Iter>
    bool strictlyMaximal(LitOrTerm pivot, Iter lits)
    {
      bool found = false;
      for (auto lit : iterTraits(lits)) {
        if (lit == pivot) {
          if (found)  {
            return false;
          } else {
            found = true;
          }
        }
        if (ordering->compare(pivot, lit) == Ordering::LESS) {
          return false;
        }
      }
      ASS(found)
      return true;
    }

    template<class NumTraits> 
    Option<LascaLiteral<NumTraits>> renormalize(Literal* l)
    {
      auto norm = this->normalizer.renormalizeLasca<NumTraits>(l);
      if (norm.isNone() || norm.unwrap().overflowOccurred) {
        return Option<LascaLiteral<NumTraits>>();
      } else {
        return Option<LascaLiteral<NumTraits>>(norm.unwrap().value);
      }
    }

  };

#if VDEBUG
  shared_ptr<LascaState> testLascaState(
    Options::UnificationWithAbstraction uwa = Options::UnificationWithAbstraction::LASCA1,
    bool strongNormalization = false,
    Ordering* ordering = nullptr
    );
#endif

}

////////////////////////////////////////////////////////////////////////////
// impl InequalityLiteral
/////////////////////////////
  
namespace Kernel {

template<class NumTraits>
Option<MaybeOverflow<InequalityLiteral<NumTraits>>> InequalityNormalizer::renormalizeIneq(Literal* lit) const
{
  using Opt = Option<MaybeOverflow<InequalityLiteral<NumTraits>>>;
  return normalizeLasca<NumTraits>(lit)
    .andThen([](auto overflown) {
      // The literal must have been normalized before, hence normalizing again can't produce more than one literal
      ASS_EQ(overflown.value.size(), 1) 
      if (overflown.value[0].isInequality()) {
        return Opt(overflown.map([](auto lit) { return InequalityLiteral<NumTraits>(std::move(lit)); }));
      } else {
        return Opt();
      }
    });
}


template<class Numeral>
Numeral normalizeFactors_divide(Numeral gcd, Numeral toCorrect)  
{ return toCorrect / gcd; }

IntegerConstantType normalizeFactors_divide(IntegerConstantType gcd, IntegerConstantType toCorrect);

template<class Numeral>
Numeral normalizeFactors_gcd(Numeral l, Numeral r)
{
  auto lcm = [](auto l, auto r) { return (l * r).intDivide(IntegerConstantType::gcd(l,r)); };
  return Numeral(
      IntegerConstantType::gcd(l.numerator()  , r.numerator()  ),
                           lcm(l.denominator(), r.denominator()));
}

IntegerConstantType normalizeFactors_gcd(IntegerConstantType l, IntegerConstantType r);

template<class NumTraits>
auto normalizeFactors(Perfect<Polynom<NumTraits>> in) -> MaybeOverflow<Perfect<Polynom<NumTraits>>>
{
  return catchOverflow([&](){

    if (in->nSummands() == 0) {
      return in;
    }
    auto gcd = fold(in->iterSummands()
      .map([](auto s) { return s.numeral.abs(); }),
      [](auto l, auto r) { return normalizeFactors_gcd(l,r); }
    );
    ASS_REP(gcd >= NumTraits::constant(0), gcd)
    if (gcd == NumTraits::constant(1) || gcd == NumTraits::constant(0)) {
      return in;
    } else {
      auto  out = perfect(Polynom<NumTraits>(in->iterSummands()
            .map([=](auto s) { return Monom<NumTraits>(normalizeFactors_divide(gcd, s.numeral), s.factors); })
            .template collect<Stack>()));
      return out;
    }
  }, in);
}

template<class NumTraits>
Option<MaybeOverflow<LascaLiteral<NumTraits>>> InequalityNormalizer::renormalizeLasca(Literal* lit) const
{
  return normalizeLasca<NumTraits>(lit)
    .map([](auto&& lits) -> MaybeOverflow<LascaLiteral<NumTraits>> { 
        return lits.map([](auto&& lits) -> LascaLiteral<NumTraits> { 
          ASS_REP(lits.size() == 1, "literal has not been normalized before.");
          return std::move(lits[0]);
        });
    });
}

template<class NumTraits>
Option<MaybeOverflow<Stack<LascaLiteral<NumTraits>>>> InequalityNormalizer::normalizeLasca(Literal* lit) const
{
  CALL("InequalityLiteral<NumTraits>::fromLiteral(Literal*)")
  DEBUG("in: ", *lit, " (", NumTraits::name(), ")")

  auto impl = [&]() {

    constexpr bool isInt = std::is_same<NumTraits, IntTraits>::value;

    using Opt = Option<MaybeOverflow<Stack<LascaLiteral<NumTraits>>>>;

    auto f = lit->functor();
    if (!theory->isInterpretedPredicate(f))
      return Opt();

    auto itp = theory->interpretPredicate(f);


    LascaPredicate pred;
    TermList l, r; // <- we rewrite to l < r or l <= r
    switch(itp) {
      case Interpretation::EQUAL:/* l == r or l != r */
        if (SortHelper::getEqualityArgumentSort(lit) != NumTraits::sort()) 
          return Opt();
        if (*lit->nthArgument(0) == NumTraits::zero()) {
          l = *lit->nthArgument(0);
          r = *lit->nthArgument(1);
        } else {
          l = *lit->nthArgument(1);
          r = *lit->nthArgument(0);
        }
        pred = lit->isPositive() ? LascaPredicate::EQ : LascaPredicate::NEQ;
        break;

      case NumTraits::leqI: /* l <= r */
        l = *lit->nthArgument(0);
        r = *lit->nthArgument(1);
        pred = LascaPredicate::GREATER_EQ;
        break;

      case NumTraits::geqI: /* l >= r ==> r <= l */
        l = *lit->nthArgument(1);
        r = *lit->nthArgument(0);
        pred = LascaPredicate::GREATER_EQ;
        break;

      case NumTraits::lessI: /* l < r */
        l = *lit->nthArgument(0);
        r = *lit->nthArgument(1);
        pred = LascaPredicate::GREATER;
        break;

      case NumTraits::greaterI: /* l > r ==> r < l */
        l = *lit->nthArgument(1);
        r = *lit->nthArgument(0);
        pred = LascaPredicate::GREATER;
        break;

      default: 
        return Opt();
    }

    if (lit->isNegative() && isInequality(pred)) {
      // ~(l >= r) <==> (r < l)
      std::swap(l, r);
      pred = pred == LascaPredicate::GREATER ? LascaPredicate::GREATER_EQ : LascaPredicate::GREATER;
    }

    if (isInt && pred == LascaPredicate::GREATER_EQ) {
      /* l <= r ==> l < r + 1 */
      r = NumTraits::add(r, NumTraits::one());
      pred = LascaPredicate::GREATER;
    }

    /* l < r ==> r > l ==> r - l > 0 */
    auto t = l == NumTraits::zero() ? r 
           : r == NumTraits::zero() ? NumTraits::minus(l)
           : NumTraits::add(r, NumTraits::minus(l));

    ASS(!isInt || pred != LascaPredicate::GREATER_EQ)
    auto tt = TypedTermList(t, NumTraits::sort());
    auto norm = Kernel::normalizeTerm(tt);
    auto simpl = _eval.evaluate(norm);
    auto simplValue = (simpl.value || norm).wrapPoly<NumTraits>();
    simplValue->integrity();
    auto factorsNormalized = normalizeFactors(simplValue);

    Stack<LascaLiteral<NumTraits>> out;
    if (_strong && pred == LascaPredicate::GREATER_EQ) {
      // t >= 0 ==> t > 0 \/ t == 0
      out = { LascaLiteral<NumTraits>(factorsNormalized.value, LascaPredicate::GREATER)
            , LascaLiteral<NumTraits>(factorsNormalized.value, LascaPredicate::EQ     ) };
    } else if (_strong && pred == LascaPredicate::NEQ) {
      // t != 0 ==> t > 0 \/ -t > 0
      out = { LascaLiteral<NumTraits>( factorsNormalized.value, LascaPredicate::GREATER)
            , LascaLiteral<NumTraits>(-factorsNormalized.value, LascaPredicate::GREATER) };
    } else {
      out = { LascaLiteral<NumTraits>(factorsNormalized.value, pred) };
    }

    return Opt(maybeOverflow(std::move(out), simpl.overflowOccurred || factorsNormalized.overflowOccurred));
  };
  auto out = impl();
  DEBUG("out: ", out);
  return out;
}


////////////////////////////////////////////////////////////////////////////
// impl LascaState
/////////////////////////////

template<class GetElem, class Cmp>
auto maxElements(GetElem getElem, unsigned size, Cmp compare, bool strictlyMax) -> Stack<decltype(getElem(0))> 
{
  Stack<decltype(getElem(0))> max(size); // TODO not sure whether this size allocation brings an advantage
  for (unsigned i = 0; i < size; i++) {
    auto isMax = [&]() {
      for (unsigned j = 0; j < size; j++) {
        if (i != j) {
          auto cmp = compare(getElem(i), getElem(j));
          switch(cmp) {

          case Ordering::LESS: return false;
          case Ordering::EQUAL:
            if (!strictlyMax) { /* ok */ break; }
            else              { return false; }
          case Ordering::INCOMPARABLE:
          case Ordering::GREATER:
            /* ok */
            break;
          default:
            ASSERTION_VIOLATION_REP(cmp)
          }
        }
      }
      return true;
    }();
    
    if (isMax)
      max.push(getElem(i));
  }
  return max;
}


// template<class GetSummand> auto LascaState::iterSelectedTerms(GetSummand getSummand, unsigned litSize, bool strictlyMax)
// {
//   return iterTraits(ownedArrayishIterator(
//       maxElements([=](unsigned i) { return i; }, litSize,
//                      [&](auto l, auto r) { return ordering->compare(getSummand(l).factors->denormalize(), getSummand(r).factors->denormalize()); },
//                      strictlyMax)
//       ))
//     .filter([=](unsigned i) { return !getSummand(i).isVar(); }) ;
// }


// TODO check whether superposition modulo LA uses strictly max
// template<class NumTraits>
//
// Stack<Monom<NumTraits>> LascaState::iterSelectedTerms(LascaLiteral<NumTraits>const& lit, bool strictlyMax)
// template<class Sum, class GetSummand> 
// auto LascaState::iterSelectedTerms(Sum lit, unsigned sumSize, GetSummand getSummand, bool strictlyMax) -> Stack<decltype(lit(sz))>;
// {

//   auto max = maxElements([&](auto i) { return getSummand; }, 
//                      sumSize,
//                      [&](auto l, auto r) { return ordering->compare(l.factors->denormalize(), r.factors->denormalize()); },
//                      strictlyMax);
//
//   unsigned offs = 0;
//   for (unsigned i = 0; i < max.size(); i++) {
//     if (max[i].factors->tryVar().isSome()) {
//       /* we skip this one */
//     } else {
//       max[offs++] = max[i];
//     }
//   }
//   max.pop(max.size() - offs);
//   return max;
// }

// // TODO check whether superposition modulo LA uses strictly max
// template<class NumTraits>
// Stack<Monom<NumTraits>> LascaState::selectedTerms(LascaLiteral<NumTraits>const& lit, bool strictlyMax)
// {
//   return iterSelectedTerms([&](auto i) { return lit.term().summandAt(i); }, lit.term().nSummands(), strictlyMax)
//     .map([=](unsigned i) { return lit.term().summandAt(i); })
//     .template collect<Stack>();
// }
//
// template<class NumTraits> Stack<SelectedAtomicTerm<NumTraits>> LascaState::selectedTerms(Clause* cl, bool strictlyMaxLiterals, bool strictlyMaxTerms)
// {
//   CALL("LascaState::selectedTerms(Clause* cl)")
//
//   return iterTraits(getRangeIterator((unsigned)0, cl->numSelected()))
//     .filterMap([&](auto i) {
//         // auto i = lit_idx.second;
//         auto lit = (*cl)[i];
//
//         return normalizer.template renormalizeLasca<NumTraits>(lit)
//           .andThen([&](auto norm) -> Option<LascaLiteral<NumTraits>> {
//               return norm.overflowOccurred 
//                 ? Option<LascaLiteral<NumTraits>>()
//                 : Option<LascaLiteral<NumTraits>>(norm.value);
//               })
//           .map([&](auto irc) { 
//               return pvi(iterSelectedTerms(
//                     [=](unsigned i ) { return irc.term().summandAt(i); }, 
//                     irc.term().nSummands(),
//                     strictlyMaxTerms)
//                 .map([=](auto j)  {
//                     return SelectedAtomicTerm<NumTraits> {
//                       .litIdx = i,
//                       .literal = lit,
//                       .ircLit = irc,
//                       .termIdx = j,
//                       .self = irc.term().summandAt(j),
//                     };
//                 }));
//           });
//         })
//         .flatten()
//         .template collect<Stack>();
//
// }

Ordering::Result compare(LascaPredicate l, LascaPredicate r);

} // namespace Kernel

template<class NumTraits> struct std::hash<Kernel::LascaLiteral<NumTraits>>
{
  size_t operator()(Kernel::LascaLiteral<NumTraits> const& self) const
  {
    return Lib::HashUtils::combine(
      Lib::StlHash::hash(self._symbol),
      Lib::StlHash::hash(self._term)
    );
  }
};


#undef DEBUG
#endif // __LASCA__
