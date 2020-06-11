
template<class CommutativeMonoid>
TermEvalResult evaluateCommutativeMonoid(Term* orig, TermEvalResult* evaluatedArgs) ;

template<class ConstantType, class EvalIneq> 
LitEvalResult evaluateInequality(Literal* lit, bool strict, EvalIneq evalIneq) ;

template<class ConstantType, class EvalGround>
LitEvalResult tryEvalConstant2(Literal* lit, EvalGround fun);

template<class ConstantType, class EvalGround>
TermEvalResult tryEvalConstant1(Term* orig, TermEvalResult* evaluatedArgs, EvalGround fun);

template<class Number> 
TermEvalResult evaluateMul(TermEvalResult&& lhs, TermEvalResult&& rhs);

template<class ConstantType, class EvalGround>
TermEvalResult tryEvalConstant2(Term* orig, TermEvalResult* evaluatedArgs, EvalGround fun);

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// Helper functions
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

template<class ConstantType, class EvalGround>
LitEvalResult tryEvalConstant2(Literal* lit, EvalGround fun) {
  auto lhs = *lit->nthArgument(0);
  auto rhs = *lit->nthArgument(1);
  ConstantType l;
  ConstantType r;
  if (theory->tryInterpretConstant(lhs, l) && theory->tryInterpretConstant(rhs, r)) {
    return LitEvalResult::constant(fun(l,r));
  } else {
    return LitEvalResult::literal(lit);
  }
}


template<class ConstantType, class EvalGround>
TermEvalResult tryEvalConstant1(Term* orig, TermEvalResult* evaluatedArgs, EvalGround fun) {

  TermList lhs = evaluatedArgs[0].template unwrap<0>();
  ConstantType l;
  if (theory->tryInterpretConstant(lhs, l)) {
    return TermEvalResult::template variant<0>(TermList(theory->representConstant(fun(l))));
  } else {
    return TermEvalResult::template variant<0>(TermList(orig));
  }
}


template<class ConstantType, class EvalGround>
TermEvalResult tryEvalConstant2(Term* orig, TermEvalResult* evaluatedArgs, EvalGround fun) {

  TermList lhs = evaluatedArgs[0].template unwrap<0>();
  TermList rhs = evaluatedArgs[1].template unwrap<0>();

  ConstantType l;
  ConstantType r;
  if (theory->tryInterpretConstant(lhs, l) 
      && theory->tryInterpretConstant(rhs, r)) {
    return TermEvalResult::template variant<0>(TermList(theory->representConstant(fun(l,r))));
  } else {
    return TermEvalResult::template variant<0>(TermList(orig));
  }
}



#define IMPL_EVALUATE_FUN(interpretation, ...)\
  template<>  \
  struct FunctionEvaluator<interpretation> { \
    template<class Config> \
    static TermEvalResult evaluate(Term* orig, TermEvalResult* evaluatedArgs) \
    { \
      CALL("FunctionEvaluator<" #interpretation ">::evaluate(Term*,TermEvalResult*)"); \
      __VA_ARGS__ \
    } \
  };


///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// UNARY_MINUS 
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

template<class Number, class Config>
TermEvalResult evaluateUnaryMinus(TermEvalResult& inner) {
  auto out = inner.match<TermEvalResult>(
        [](const TermList& t) { 
        return TermEvalResult::template variant<1>(AnyPoly(
            Polynom<Number>( Number::constant(-1), t)
            ));
      }
      , [](const AnyPoly& p) {
        auto out = Polynom<Number>::template poly_mul<Config>(
              Polynom<Number>(Number::constant(-1))
            , p.as<Polynom<Number>>());

        return TermEvalResult::template variant<1>(AnyPoly(std::move(out)));
      }
      );
  return out;
}


#define IMPL_UNARY_MINUS(Const) \
  IMPL_EVALUATE_FUN(NumTraits<Const>::minusI, {\
    return evaluateUnaryMinus<NumTraits<Const>, Config>(evaluatedArgs[0]);  \
  })

  IMPL_UNARY_MINUS(RealConstantType    )
  IMPL_UNARY_MINUS(RationalConstantType)
  IMPL_UNARY_MINUS(IntegerConstantType )

#undef IMPL_UNARY_MINUS


///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// MULTIPLY
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

template<class Number, class Config> TermEvalResult evaluateMul(TermEvalResult&& lhs, TermEvalResult&& rhs) 
{
  // TODO parametrize usePolyMul
  using Poly = Polynom<Number>;
  using Const = typename Poly::Coeff;

  auto to_poly = [](TermEvalResult&& x) -> Poly {
    return std::move(x).match<Poly>(
        [](TermList&& t) { return Poly(Number::constant(1), t); }
      , [](AnyPoly&& p) { return std::move(p.as<Poly>()); }
      );
  };

  return TermEvalResult::template variant<1>(AnyPoly(
        Poly::template poly_mul<Config>(to_poly(std::move(lhs)), to_poly(std::move(rhs)))));
}


#define IMPL_MULTIPLY(Const) \
  IMPL_EVALUATE_FUN(NumTraits<Const>::mulI, { \
    return evaluateMul<NumTraits<Const>, Config>(std::move(evaluatedArgs[0]), std::move(evaluatedArgs[1])); \
  }) \

  IMPL_MULTIPLY(RealConstantType    )
  IMPL_MULTIPLY(RationalConstantType)
  IMPL_MULTIPLY(IntegerConstantType )

#undef IMPL_MULTIPLY


///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// ADD 
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

template<class Number>
Polynom<Number> evaluateAdd(TermEvalResult&& lhs, TermEvalResult&& rhs) {
  CALL("Polynom<Number> evaluateAdd(TermEvalResult&& lhs, TermEvalResult&& rhs)")
  using Const = typename Number::ConstantType;
  using Poly = Polynom<Number>;

  Poly l = std::move(lhs).match<Poly>(
        [](TermList && t) { return Poly(Number::constant(1), t); }
      , [](AnyPoly  && p) { return std::move(p.as<Poly>()); }
      );

  Poly r = std::move(rhs).match<Poly>(
        [](TermList&& t) { return Poly(Number::constant(1), t); }
      , [](AnyPoly&& p) { return std::move(p.as<Poly>()); }
      );
  
  return Poly::poly_add(l, r);
}


#define IMPL_ADD(Const) \
  IMPL_EVALUATE_FUN(NumTraits<Const>::addI, { \
    auto Poly = evaluateAdd<NumTraits<Const>>(std::move(evaluatedArgs[0]), std::move(evaluatedArgs[1])); \
    auto out = TermEvalResult::template variant<1>(AnyPoly(std::move(Poly))); \
    return out; \
  }) \

  IMPL_ADD(RealConstantType    )
  IMPL_ADD(RationalConstantType)
  IMPL_ADD(IntegerConstantType )

#undef IMPL_ADD

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// Functions that are only handled for constants
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////

#define IMPL_EVAL_UNARY(Const, INTER, expr) \
  IMPL_EVALUATE_FUN(Interpretation::INTER, { \
    return tryEvalConstant1<Const>(orig, evaluatedArgs, [] (Const x) { return expr; });  \
  } )

#define IMPL_EVAL_BINARY(Const, INTER, expr) \
  IMPL_EVALUATE_FUN(Interpretation::INTER, { \
    return tryEvalConstant2<Const>(orig, evaluatedArgs, [] (Const l, Const r) { return expr; }); \
  } )


/////////////////// Integer only functions

IMPL_EVAL_UNARY(IntegerConstantType, INT_ABS      , x >= 0 ? x : -x)
IMPL_EVAL_UNARY(IntegerConstantType, INT_SUCCESSOR, x + 1          )

/////////////////// INT_QUOTIENT_E and friends

#define IMPL_QUOTIENT_REMAINDER(Const, NUM, SUFFIX) \
  IMPL_EVAL_BINARY(Const, NUM ##  _QUOTIENT_ ## SUFFIX,  l.quotient ## SUFFIX(r)) \
  IMPL_EVAL_BINARY(Const, NUM ## _REMAINDER_ ## SUFFIX,  l - (l.quotient ## SUFFIX (r)*r)) \

#define IMPL_QUOTIENT_REMAINDERS(Const, NUM) \
  IMPL_QUOTIENT_REMAINDER(Const, NUM, E) \
  IMPL_QUOTIENT_REMAINDER(Const, NUM, T) \
  IMPL_QUOTIENT_REMAINDER(Const, NUM, F) \
  IMPL_EVAL_BINARY(Const, NUM ## _MINUS, l - r) \

  IMPL_QUOTIENT_REMAINDERS(RealConstantType    , REAL)
  IMPL_QUOTIENT_REMAINDERS(RationalConstantType, RAT )
  IMPL_QUOTIENT_REMAINDERS(IntegerConstantType , INT )

#undef IMPL_QUOTIENT_REMAINDER
#undef IMPL_QUOTIENT_REMAINDERS

/////////////////// INT_FLOOR and friends

// have no effect for ints
IMPL_EVAL_UNARY(IntegerConstantType, INT_FLOOR   , x)
IMPL_EVAL_UNARY(IntegerConstantType, INT_CEILING , x)
IMPL_EVAL_UNARY(IntegerConstantType, INT_TRUNCATE, x)
IMPL_EVAL_UNARY(IntegerConstantType, INT_ROUND   , x)

// same impl for fractionals
#define IMPL_FRAC_FLOOR_FRIENDS(Const, NUM) \
  IMPL_EVAL_UNARY(Const, NUM ## _FLOOR, x.floor()) \
  IMPL_EVAL_UNARY(Const, NUM ## _CEILING, x.ceiling()) \
  IMPL_EVAL_UNARY(Const, NUM ## _TRUNCATE, x.truncate()) \

  IMPL_FRAC_FLOOR_FRIENDS(RealConstantType    , REAL)
  IMPL_FRAC_FLOOR_FRIENDS(RationalConstantType, RAT)

#undef IMPL_EVAL_FRAC_FLOOR_FRIENDS
 
/////////////////// RAT_TO_INT and friends

#define IMPL_NUM_CVT(Const, NUM) \
    IMPL_EVAL_UNARY(Const, NUM ## _TO_INT, IntegerConstantType::floor(x)) \
    IMPL_EVAL_UNARY(Const, NUM ## _TO_RAT, RationalConstantType(x)) \
    IMPL_EVAL_UNARY(Const, NUM ## _TO_REAL, RealConstantType(x)) \

  IMPL_NUM_CVT(RealConstantType    , REAL)
  IMPL_NUM_CVT(RationalConstantType, RAT )
  IMPL_NUM_CVT(IntegerConstantType , INT )

#undef IMPL_NUM_CVT

/////////////////// QUOTIENT 
//
#define IMPL_QUOTIENT(Const, NUM) \
    IMPL_EVAL_BINARY(Const, NUM ## _QUOTIENT, l / r) \

  IMPL_QUOTIENT(RealConstantType    , REAL)
  IMPL_QUOTIENT(RationalConstantType, RAT )

#undef IMPL_QUOTIENT
 

