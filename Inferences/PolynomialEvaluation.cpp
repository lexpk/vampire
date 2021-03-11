/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Inferences/PolynomialEvaluation.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Ordering.hpp"
#include "Shell/Statistics.hpp"
#include "Lib/VirtualIterator.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/BottomUpEvaluation/PolyNf.hpp"

#define DEBUG(...) //DBG(__VA_ARGS__)
using namespace Lib;


namespace Inferences {

using LitSimplResult = SimplifyingGeneratingLiteralSimplification::Result;

PolynomialEvaluation::~PolynomialEvaluation() {}

PolynomialEvaluation::PolynomialEvaluation(Ordering& ordering) : SimplifyingGeneratingLiteralSimplification(InferenceRule::EVALUATION, ordering) {}


Literal* createLiteral(Literal* orig, PolyNf* evaluatedArgs) {
  if (orig->isEquality()) {
    return Literal::createEquality(
          orig->polarity(), 
          evaluatedArgs[0].denormalize(), 
          evaluatedArgs[1].denormalize(), 
          SortHelper::getArgSort(orig, 0));
  } else {
    auto arity = orig->arity();
    Stack<TermList> args(arity);
    for (int i = 0; i < arity; i++) {
      args.push(evaluatedArgs[i].denormalize());
    }
    return Literal::create(orig, args.begin());
  }
}

PolynomialEvaluation::Result PolynomialEvaluation::simplifyLiteral(Literal* lit) 
{
  Stack<PolyNf> terms(lit->arity());
  auto anyChange = false;
  for (int i = 0; i < lit->arity(); i++) {
    auto term = *lit->nthArgument(i);
    auto norm = PolyNf::normalize(TypedTermList(term, SortHelper::getArgSort(lit, i)));
    auto ev = evaluate(norm);
    anyChange = anyChange || ev.isSome();
    terms.push(std::move(ev).unwrapOrElse([&](){ return norm; }));
  }
  auto simplified = tryEvalPredicate(lit, terms.begin());
  anyChange = anyChange || simplified.isSome();

  return anyChange 
      ? std::move(simplified)
        .unwrapOrElse([&]()
          { return LitSimplResult::literal(createLiteral(lit, terms.begin())); })
      : LitSimplResult::literal(lit);
}

#include "Kernel/PolynomialNormalizer/PredicateEvaluator.hpp"

Option<LitSimplResult> PolynomialEvaluation::tryEvalPredicate(Literal* orig, PolyNf* evaluatedArgs) const {
  CALL("PolynomialEvaluation::tryEvalPredicate(Literal* term)")
  DEBUG("evaluating: ", orig->toString());

#define HANDLE_CASE(INTER) case Interpretation::INTER: return PredicateEvaluator<Interpretation::INTER>::evaluate(orig, evaluatedArgs); 
#define IGNORE_CASE(INTER) case Interpretation::INTER: return Option<LitSimplResult>();
#define HANDLE_NUM_CASES(NUM)                                                                                 \
      HANDLE_CASE(NUM ## _IS_INT)                                                                             \
      HANDLE_CASE(NUM ## _IS_RAT)                                                                             \
      HANDLE_CASE(NUM ## _IS_REAL)                                                                            \
      HANDLE_CASE(NUM ## _GREATER)                                                                            \
      HANDLE_CASE(NUM ## _GREATER_EQUAL)                                                                      \
      HANDLE_CASE(NUM ## _LESS)                                                                               \
      HANDLE_CASE(NUM ## _LESS_EQUAL) 

  auto sym = env.signature->getPredicate(orig->functor());
  if (sym->interpreted()) {
    auto inter = static_cast<Signature::InterpretedSymbol*>(sym)->getInterpretation();

    switch (inter) {
      /* polymorphic */
      HANDLE_CASE(EQUAL)

      /* common number predicates */
      HANDLE_NUM_CASES(INT)
      HANDLE_NUM_CASES(RAT)
      HANDLE_NUM_CASES(REAL)

      /* integer predicates */
      HANDLE_CASE(INT_DIVIDES)

      default:
        // WARN("WARNING: unexpected interpreted predicate: ", lit->toString())
        ASSERTION_VIOLATION
        return Option<LitSimplResult>();
    }
  } else {
    return Option<LitSimplResult>();
  }

#undef HANDLE_CASE
#undef IGNORE_CASE
#undef HANDLE_NUM_CASES
}

#include "Inferences/FunctionEvaluation.cpp"

Option<PolyNf> trySimplify(Theory::Interpretation i, PolyNf* evalArgs) 
{
  CALL("trySimplify(Theory::Interpretation i, PolyNf* evalArgs) ")
  try {
    switch (i) {

#define CONSTANT_CASE_2(Num, func, expr)                                                                      \
      case Num##Traits:: func ## I:                                                                           \
        {                                                                                                     \
          using Const = typename Num##Traits::ConstantType;                                                   \
          return trySimplifyConst2<Num##Traits>(evalArgs, [](Const l, Const r){ return expr; });              \
        }                                                                                                     \

#define CASE(inter)                                                                                           \
      case inter: return FunctionEvaluator<inter>::simplify(evalArgs);

#define QUOTIENT_REMAINDER_CASES(X)                                                                           \
      CASE(Theory::INT_QUOTIENT_  ## X)                                                                       \
      CASE(Theory::INT_REMAINDER_ ## X)

#define FRAC_CASE(Num)                                                                                        \
      CASE(Num##Traits::divI)

#define NUM_CASE(Num)                                                                                         \
      case Num ## Traits::minusI: return trySimplifyUnaryMinus<Num ## Traits>(evalArgs);

      NUM_CASE(Int)
      NUM_CASE(Rat)
      NUM_CASE(Real)
      QUOTIENT_REMAINDER_CASES(E)
      QUOTIENT_REMAINDER_CASES(T)
      QUOTIENT_REMAINDER_CASES(F)

      FRAC_CASE(Rat)
      FRAC_CASE(Real)

  // TODO evaluate conversion functions
  // TODO evaluate INT_ABS
  // TODO evaluate INT_SUCCESSOR
  // TODO evaluate FRAC_QUOTIENT
  // TODO evaluate FRAC_ROUND
  // TODO evaluate NUM_TO_NUM
  // TODO evaluate NUM_TRUNCATE

#undef NUM_CASE
#undef QUOTIENT_REMAINDER_CASES
#undef CONSTANT_CASE

      default:
        return none<PolyNf>();
    }
  } catch (MachineArithmeticException&) {
    return none<PolyNf>();

  } catch (DivByZeroException&) {
    return none<PolyNf>();
  }
}


Option<PolyNf> PolynomialEvaluation::evaluate(TermList term, unsigned sortNumber) const 
{ return evaluate(TypedTermList(term, sortNumber)); }

Option<PolyNf> PolynomialEvaluation::evaluate(Term* term) const 
{ return evaluate(TypedTermList(term)); }

Option<PolyNf> PolynomialEvaluation::evaluate(TypedTermList term) const 
{ return evaluate(PolyNf::normalize(term)); }

template<class Number>
Polynom<Number> simplifyPoly(Polynom<Number> const& in, PolyNf* simplifiedArgs);

template<class Number>
Monom<Number> simplifyMonom(Monom<Number> const&, PolyNf* simplifiedArgs);

POLYMORPHIC_FUNCTION(AnyPoly, SimplifyPoly  , const& p, PolyNf* ts;) 
{ return AnyPoly(perfect(simplifyPoly(*p, ts))); }

AnyPoly simplifyPoly(AnyPoly const& p, PolyNf* ts)
{ return p.apply(Polymorphic::SimplifyPoly{ ts }); }

Option<PolyNf> PolynomialEvaluation::evaluate(PolyNf normalized) const 
{
  CALL("PolynomialEvaluation::evaluate(TypedTermList term) const")

  DEBUG("evaluating ", normalized)
  struct Eval 
  {
    const PolynomialEvaluation& norm;

    using Result = PolyNf;
    using Arg    = PolyNf;

    PolyNf operator()(PolyNf orig, PolyNf* ts) 
    { 
      return orig.match(
          [&](Perfect<FuncTerm> f)  -> PolyNf
          { 
            return f->function().tryInterpret()
              .andThen( [&](Theory::Interpretation && i)  -> Option<PolyNf>
                { return trySimplify(i, ts); })
              .unwrapOrElse([&]() -> PolyNf
                { return PolyNf(perfect(FuncTerm(f->function(), ts))); });

          }, 

          [&](Variable v) 
          { return v; },

          [&](AnyPoly p) 
          { return simplifyPoly(p, ts); }
      );
    }
  };
  static Memo::Hashed<PolyNf, PolyNf> memo;
  auto out = evaluateBottomUp(normalized, Eval{ *this }, memo);
  if (out == normalized) {
    return Option<PolyNf>();
  } else {
    return Option<PolyNf>(out);
  }
}

template<class Config>
PolyNf createTerm(unsigned fun, PolyNf* evaluatedArgs) 
{ return perfect(FuncTerm(FuncId(fun), evaluatedArgs)); }

template<class Number>
Polynom<Number> PolynomialEvaluation::simplifySummation(Stack<Monom<Number>> summands)
{ 
  CALL("simplifySummation(Stack<Monom<Number>>)") 
  using Monom   = Monom<Number>;
  using Polynom = Polynom<Number>;
  try {

    // then we sort them by their monom, in order to add up the coefficients efficiently
    std::sort(summands.begin(), summands.end());

    // add up the coefficients (in place)
    {
      auto offs = 0;
      for (unsigned i = 0; i < summands.size(); i++) { 
        auto monom = summands[i];
        auto numeral = monom.numeral;
        auto factors = monom.factors;
        while ( i + 1 < summands.size() && summands[i+1].factors == factors ) {
          numeral = numeral + summands[i+1].numeral;
          i++;
        }
        if (numeral != Number::zeroC) 
          summands[offs++] = Monom(numeral, factors);
      }
      summands.truncate(offs);
    }

    auto poly = Polynom(std::move(summands));
    poly.integrity();
    return poly;
  } catch (ArithmeticException&) { 
    return Polynom(std::move(summands));
  }
}

template Polynom< IntTraits> PolynomialEvaluation::simplifySummation< IntTraits>(Stack<Monom< IntTraits>> summands);
template Polynom< RatTraits> PolynomialEvaluation::simplifySummation< RatTraits>(Stack<Monom< RatTraits>> summands);
template Polynom<RealTraits> PolynomialEvaluation::simplifySummation<RealTraits>(Stack<Monom<RealTraits>> summands);



template<class Number>
Polynom<Number> simplifyPoly(Polynom<Number> const& in, PolyNf* simplifiedArgs)
{ 
  CALL("simplify(Polynom<Number>const&, PolyNf* simplifiedArgs)") 
  using Monom   = Monom<Number>;
  try {

    // first we simplify all the monoms containted in this polynom
    Stack<Monom> out;
    {
      auto offs = 0;
      for (unsigned i = 0; i < in.nSummands(); i++) {
        auto monom  = in.summandAt(i);
        auto simpl = simplifyMonom(monom, &simplifiedArgs[offs]);
        if (simpl.numeral == Number::zeroC) {
          /* we don't add it */
        } else if (simpl.factors->nFactors() == 1 && simpl.factors->factorAt(0).tryPolynom().isSome()) {
          auto poly = simpl.factors->factorAt(0).tryPolynom().unwrap();
          for (auto fac : poly->iterSummands()) {
            fac.numeral = fac.numeral * simpl.numeral;
            out.push(fac);
          }
        } else {
          out.push(simpl);
        }
        offs += monom.factors->nFactors();
      }
    }

    return PolynomialEvaluation::simplifySummation(std::move(out));
  } catch (ArithmeticException&) { 
    return in.replaceTerms(simplifiedArgs);
  }
}


/** Simplifies the factors of a monom. 
 * In exact this means, that all the numeral factors are collapsed into one numeral (e.g. 3*4*3*x ==> 36*x)
 */
template<class Number>
Monom<Number> simplifyMonom(Monom<Number> const& in, PolyNf* simplifiedArgs) 
{ 

  using Numeral      = typename Number::ConstantType;
  using Monom        = Monom<Number>;
  using MonomFactor  = MonomFactor<Number>;
  using MonomFactors = MonomFactors<Number>;

  auto pow = [](Numeral c, int power) -> Numeral {
    ASS(power > 0)
    auto out = c;
    while (--power > 0) {
      out = out * c;
    }
    return out;
  };

  auto& facs = *in.factors;
  Stack<MonomFactor> args(facs.nFactors());
  for (unsigned i = 0; i < facs.nFactors(); i++) {
    args.push(MonomFactor(simplifiedArgs[i], facs.factorAt(i).power));
  }

  std::sort(args.begin(), args.end());

  auto offs = 0;
  auto numeral = in.numeral;
  for (unsigned i = 0; i < facs.nFactors(); i++) {
    auto& arg = args[i];
    auto c = arg.term.template tryNumeral<Number>();
    if (c.isSome()) {
      // arg is a number constant
      numeral = numeral * pow(c.unwrap(), arg.power);
    } else {
      // arg is a non-number term
      auto term  = arg.term;
      auto power = arg.power;
      while (i + 1 < facs.nFactors() && args[i + 1].term == term) {
        power += args[i + 1].power;
        i++;
      }
      if (power != 0)
        args[offs++] = MonomFactor(term, power);
    }
  }


  if (numeral == Numeral(0)) {
    return Monom::zero();
  } else {
    args.truncate(offs);
    return Monom(numeral, perfect(MonomFactors(std::move(args)))); 
  }
}



} // Inferences