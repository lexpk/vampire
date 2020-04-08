
/*
 * File TheoryAxioms.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file TheoryAxioms.cpp
 * Implements class TheoryAxioms.
 */

#include "Lib/Environment.hpp"
#include "Lib/Stack.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Sorts.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Theory.hpp"

#include "Property.hpp"
#include "SymCounter.hpp"
#include "TheoryAxioms.hpp"
#include "Options.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Shell;


/**
 * Add the unit @c to @c problem and output it, if the option show_theory_axioms is on.
 * @since 11/11/2013 Manchester
 * @author Andrei Voronkov
 */
void TheoryAxioms::addAndOutputTheoryUnit(Unit* unit, unsigned level)
{
  CALL("TheoryAxioms::addAndOutputTheoryUnit");

  static Options::TheoryAxiomLevel opt_level = env.options->theoryAxioms();
  // if the theory axioms are some or off (want this case for some things like fool) and the axiom is not
  // a cheap one then don't add it
  if(opt_level != Options::TheoryAxiomLevel::ON && level != CHEAP){ return; }


  if (env.options->showTheoryAxioms()) {
    Unit* qunit = unit;
    Formula* f = 0;
    if(unit->isClause()){
      f = Formula::fromClause(static_cast<Clause*>(unit));
      qunit = new FormulaUnit(f,unit->inference(),unit->inputType());
    }
    cout << "% Theory " << (unit->isClause() ? "clause" : "formula" ) << ": " << qunit->toString() << "\n";
    if(f){ f->destroy(); } 
  }
  if(!unit->isClause()){
    _prb.reportFormulasAdded();
  }
  UnitList::push(unit, _prb.units());
} // addAndOutputTheoryUnit

/**
 * Add the theory unit clause with literal @c lit to @c problem.
 * @since 11/11/2013, Manchester: output of the clause added
 * @author Andrei Voronkov
 */
void TheoryAxioms::addTheoryUnitClause(Literal* lit, unsigned level)
{
  CALL("TheoryAxioms::addTheoryUnitClause");
  addTheoryUnitClause(lit, new Inference(Inference::THEORY_AXIOM), level);
} // addTheoryUnitClause

void TheoryAxioms::addTheoryUnitClause(Literal* lit, Inference* inf, unsigned level)
{
  CALL("TheoryAxioms::addTheoryUnitClause");
  Clause* unit = Clause::fromIterator(getSingletonIterator(lit), Unit::AXIOM, inf);
  addAndOutputTheoryUnit(unit, level);
} // addTheoryUnitClause

void TheoryAxioms::addTheoryNonUnitClause(Literal* lit1, Literal* lit2,unsigned level)
{
  CALL("TheoryAxioms::addTheoryNonUnitClause");
  LiteralStack lits;
  ASS(lit1);
  lits.push(lit1);
  ASS(lit2);
  lits.push(lit2);
  Clause* cl = Clause::fromStack(lits, Unit::AXIOM, new Inference(Inference::THEORY_AXIOM));
  addAndOutputTheoryUnit(cl, level);
} // addTheoryNonUnitCLause

void TheoryAxioms::addTheoryNonUnitClause(Literal* lit1, Literal* lit2, Literal* lit3,unsigned level)
{
  CALL("TheoryAxioms::addTheoryNonUnitClause");
  LiteralStack lits;
  ASS(lit1);
  lits.push(lit1);
  ASS(lit2);
  lits.push(lit2);
  if (lit3) {
    lits.push(lit3);
  }
  Clause* cl = Clause::fromStack(lits, Unit::AXIOM, new Inference(Inference::THEORY_AXIOM));
  addAndOutputTheoryUnit(cl, level);
} // addTheoryNonUnitCLause

void TheoryAxioms::addTheoryNonUnitClause(Literal* lit1, Literal* lit2, Literal* lit3,Literal* lit4,unsigned level)
{
  CALL("TheoryAxioms::addTheoryNonUnitClause");
  LiteralStack lits;
  ASS(lit1);
  lits.push(lit1);
  ASS(lit2);
  lits.push(lit2);
  ASS(lit3);
  lits.push(lit3);
  ASS(lit4);
  lits.push(lit4);
  Clause* cl = Clause::fromStack(lits, Unit::AXIOM, new Inference(Inference::THEORY_AXIOM));
  addAndOutputTheoryUnit(cl, level);
} // addTheoryNonUnitCLause

/**
 * Add the axiom f(X,Y)=f(Y,X).
 * @since 11/11/2013, Manchester: modified
 * @author Andrei Voronkov
 */
void TheoryAxioms::addCommutativity(Interpretation op)
{
  CALL("TheoryAxioms::addCommutativity");
  ASS(theory->isFunction(op));
  ASS_EQ(theory->getArity(op),2);

  unsigned f = env.signature->getInterpretingSymbol(op);
  unsigned srt = theory->getOperationSort(op);
  TermList x(0,false);
  TermList y(1,false);
  TermList fxy(Term::create2(f,x,y));
  TermList fyx(Term::create2(f,y,x));
  Literal* eq = Literal::createEquality(true,fxy,fyx,srt);
  addTheoryUnitClause(eq, EXPENSIVE);
} // addCommutativity

/**
 * Add axiom f(X,f(Y,Z))=f(f(X,Y),Z).
 * @since 11/11/2013, Manchester: modified
 * @author Andrei Voronkov
 */
void TheoryAxioms::addAssociativity(Interpretation op)
{
  CALL("TheoryAxioms::addCommutativity");
  ASS(theory->isFunction(op));
  ASS_EQ(theory->getArity(op),2);

  unsigned f = env.signature->getInterpretingSymbol(op);
  unsigned srt = theory->getOperationSort(op);
  TermList x(0,false);
  TermList y(1,false);
  TermList z(2,false);
  TermList fxy(Term::create2(f,x,y));
  TermList fyz(Term::create2(f,y,z));
  TermList fx_fyz(Term::create2(f,x,fyz));
  TermList f_fxy_z(Term::create2(f,fxy,z));
  Literal* eq = Literal::createEquality(true, fx_fyz,f_fxy_z, srt);
  addTheoryUnitClause(eq, EXPENSIVE);
} // addAsssociativity


/**
 * Add axiom f(X,e)=X.
 * @since 11/11/2013, Manchester: modified
 * @author Andrei Voronkov
 */
void TheoryAxioms::addRightIdentity(Interpretation op, TermList e)
{
  CALL("TheoryAxioms::addRightIdentity");
  ASS(theory->isFunction(op));
  ASS_EQ(theory->getArity(op),2);

  unsigned f = env.signature->getInterpretingSymbol(op);
  unsigned srt = theory->getOperationSort(op);
  TermList x(0,false);
  TermList fxe(Term::create2(f,x,e));
  Literal* eq = Literal::createEquality(true,fxe,x,srt);
  addTheoryUnitClause(eq, EXPENSIVE);
} // addRightIdentity

/**
 * Add axiom f(e,X)=X.
 */
void TheoryAxioms::addLeftIdentity(Interpretation op, TermList e)
{
  CALL("TheoryAxioms::addLeftIdentity");
  ASS(theory->isFunction(op));
  ASS_EQ(theory->getArity(op),2);

  unsigned f = env.signature->getInterpretingSymbol(op);
  unsigned srt = theory->getOperationSort(op);
  TermList x(0,false);
  TermList fex(Term::create2(f,e,x));
  Literal* eq = Literal::createEquality(true,fex,x,srt);
  addTheoryUnitClause(eq, EXPENSIVE);
} // addLeftIdentity

/**
 * Add axioms for commutative group with addition @c op, inverse @c inverse and unit @c e:
 * <ol>
 * <li>f(X,Y)=f(Y,X) (commutativity)</li>
 * <li>f(X,f(Y,Z))=f(f(X,Y),Z) (associativity)</li>
 * <li>f(X,e)=X (right identity)</li>
 * <li>i(f(x,y)) = f(i(y),i(x))</li>
 * <li>f(x,i(x))=e (right inverse)</li>
 * </ol>
 * @since 11/11/2013, Manchester: modified
 * @author Andrei Voronkov
 */
void TheoryAxioms::addCommutativeGroupAxioms(Interpretation op, Interpretation inverse, TermList e)
{
  CALL("TheoryAxioms::addCommutativeGroupAxioms");

  ASS(theory->isFunction(op));
  ASS_EQ(theory->getArity(op),2);
  ASS(theory->isFunction(inverse));
  ASS_EQ(theory->getArity(inverse),1);

  addCommutativity(op);
  addAssociativity(op);
  addRightIdentity(op,e);

  // i(f(x,y)) = f(i(y),i(x))
  unsigned f = env.signature->getInterpretingSymbol(op);
  unsigned i = env.signature->getInterpretingSymbol(inverse);
  unsigned srt = theory->getOperationSort(op);
  ASS_EQ(srt, theory->getOperationSort(inverse));

  TermList x(0,false);
  TermList y(1,false);
  TermList fxy(Term::create2(f,x,y));
  TermList ix(Term::create1(i,x));
  TermList iy(Term::create1(i,y));
  TermList i_fxy(Term::create1(i,fxy));
  TermList f_iy_ix(Term::create2(f,iy,ix));
  Literal* eq1 = Literal::createEquality(true,i_fxy,f_iy_ix,srt);
  addTheoryUnitClause(eq1, EXPENSIVE);

  // f(x,i(x))=e
  TermList fx_ix(Term::create2(f,x,ix));
  Literal* eq2 = Literal::createEquality(true,fx_ix,e,srt);
  addTheoryUnitClause(eq2, EXPENSIVE);
} // TheoryAxioms::addCommutativeGroupAxioms

/**
 * Add axiom op(op(x,i(y)),y) = x
 * e.g. (x+(-y))+y = x
 */
void TheoryAxioms::addRightInverse(Interpretation op, Interpretation inverse)
{
  TermList x(0,false);
  TermList y(0,false);
  unsigned f = env.signature->getInterpretingSymbol(op);
  unsigned i = env.signature->getInterpretingSymbol(inverse);
  unsigned srt = theory->getOperationSort(op);
  ASS_EQ(srt, theory->getOperationSort(inverse));

  TermList iy(Term::create1(i,y));
  TermList xiy(Term::create2(f,x,iy));
  TermList xiyy(Term::create2(f,xiy,y));
  Literal* eq = Literal::createEquality(true,xiyy,x,srt);
  addTheoryUnitClause(eq, EXPENSIVE);
}

/**
 * Add axiom ~op(X,X)
 */
void TheoryAxioms::addNonReflexivity(Interpretation op)
{
  CALL("TheoryAxioms::addNonReflexivity");

  ASS(!theory->isFunction(op));
  ASS_EQ(theory->getArity(op),2);

  unsigned opPred = env.signature->getInterpretingSymbol(op);
  TermList x(0,false);
  Literal* l11 = Literal::create2(opPred, false, x, x);
  addTheoryUnitClause(l11, CHEAP);
} // addNonReflexivity

/**
 * Add axiom ~op(X,Y) | ~op(Y,Z) | op(X,Z)
 */
void TheoryAxioms::addTransitivity(Interpretation op)
{
  CALL("TheoryAxioms::addTransitivity");
  ASS(!theory->isFunction(op));
  ASS_EQ(theory->getArity(op),2);

  unsigned opPred = env.signature->getInterpretingSymbol(op);
  TermList x(0,false);
  TermList y(1,false);
  TermList v3(2,false);

  Literal* nonL12 = Literal::create2(opPred, false, x, y);
  Literal* nonL23 = Literal::create2(opPred, false, y, v3);
  Literal* l13 = Literal::create2(opPred, true, x, v3);

  addTheoryNonUnitClause(nonL12, nonL23, l13,CHEAP);
}

/**
 * Add axiom less(X,Y) | less(Y,X) | X=Y
 */
void TheoryAxioms::addOrderingTotality(Interpretation less)
{
  CALL("TheoryAxioms::addOrderingTotality");
  ASS(!theory->isFunction(less));
  ASS_EQ(theory->getArity(less),2);

  unsigned opPred = env.signature->getInterpretingSymbol(less);
  TermList x(0,false);
  TermList y(1,false);

  Literal* l12 = Literal::create2(opPred, true, x, y);
  Literal* l21 = Literal::create2(opPred, true, y, x);

  unsigned srt = theory->getOperationSort(less);
  Literal* eq = Literal::createEquality(true,x,y,srt);

  addTheoryNonUnitClause(l12, l21,eq,CHEAP);
}

/**
 * Add axioms of reflexivity, transitivity and total ordering for predicate @c less
 */
void TheoryAxioms::addTotalOrderAxioms(Interpretation less)
{
  CALL("TheoryAxioms::addTotalOrderAxioms");

  addNonReflexivity(less);
  addTransitivity(less);
  addOrderingTotality(less);
}

/**
 * Add axiom ~less(X,Y) | less(X+Z,Y+Z)
 */
void TheoryAxioms::addMonotonicity(Interpretation less, Interpretation addition)
{
  CALL("TheoryAxioms::addMonotonicity");
  ASS(!theory->isFunction(less));
  ASS_EQ(theory->getArity(less),2);
  ASS(theory->isFunction(addition));
  ASS_EQ(theory->getArity(addition),2);

  unsigned lessPred = env.signature->getInterpretingSymbol(less);
  unsigned addFun = env.signature->getInterpretingSymbol(addition);
  TermList x(0,false);
  TermList y(1,false);
  TermList v3(2,false);
  TermList xPv3(Term::create2(addFun, x,v3));
  TermList yPv3(Term::create2(addFun, y,v3));
  Literal* nonLe = Literal::create2(lessPred, false, x, y);
  Literal* leAdded = Literal::create2(lessPred, true, xPv3, yPv3);

  addTheoryNonUnitClause(nonLe, leAdded,EXPENSIVE);
}

/**
 * Add the axiom $less(X,$sum(X,1))
 *
 * Taken from SPASS+T work
 */
void TheoryAxioms::addPlusOneGreater(Interpretation plus, TermList oneElement,
                                     Interpretation less)
{
  CALL("TheoryAxioms::addPlusOneGreater");
  ASS(!theory->isFunction(less));
  ASS_EQ(theory->getArity(less),2);
  ASS(theory->isFunction(plus));
  ASS_EQ(theory->getArity(plus),2);

  unsigned lessPred = env.signature->getInterpretingSymbol(less);
  unsigned addFun = env.signature->getInterpretingSymbol(plus);
  TermList x(0,false);

  TermList xPo(Term::create2(addFun,x,oneElement));
  Literal* xPo_g_x = Literal::create2(lessPred,true,x,xPo);
  addTheoryUnitClause(xPo_g_x,CHEAP);
}

/**
 * Add axioms for addition, unary minus and ordering
 */
void TheoryAxioms::addAdditionAndOrderingAxioms(Interpretation plus, Interpretation unaryMinus,
    TermList zeroElement, TermList oneElement, Interpretation less)
{
  CALL("TheoryAxioms::addAdditionAndOrderingAxioms");

  addCommutativeGroupAxioms(plus, unaryMinus, zeroElement);
  addTotalOrderAxioms(less);
  addMonotonicity(less, plus);

  // y < x+one | x<y
  unsigned plusFun = env.signature->getInterpretingSymbol(plus);
  unsigned lessPred = env.signature->getInterpretingSymbol(less);
  TermList x(0,false);
  TermList y(1,false);
  Literal* xLy = Literal::create2(lessPred,true,x,y);
  TermList xP(Term::create2(plusFun,x,oneElement));
  Literal* yLxP = Literal::create2(lessPred,true,y,xP);
  addTheoryNonUnitClause(xLy,yLxP,EXPENSIVE);

  // add that --x = x
  unsigned varSort = theory->getOperationSort(unaryMinus);
  unsigned unaryMinusFun = env.signature->getInterpretingSymbol(unaryMinus);
  TermList mx(Term::create1(unaryMinusFun,x));
  TermList mmx(Term::create1(unaryMinusFun,mx));
  Literal* mmxEqx = Literal::createEquality(true,mmx,x,varSort);
  addTheoryUnitClause(mmxEqx, EXPENSIVE);

}

/**
 * Add axioms for addition, multiplication, unary minus and ordering
 */
void TheoryAxioms::addAdditionOrderingAndMultiplicationAxioms(Interpretation plus, Interpretation unaryMinus,
    TermList zeroElement, TermList oneElement, Interpretation less, Interpretation multiply)
{
  CALL("TheoryAxioms::addAdditionOrderingAndMultiplicationAxioms");

  unsigned srt = theory->getOperationSort(plus);
  ASS_EQ(srt, theory->getOperationSort(unaryMinus));
  ASS_EQ(srt, theory->getOperationSort(less));
  ASS_EQ(srt, theory->getOperationSort(multiply));

  addAdditionAndOrderingAxioms(plus, unaryMinus, zeroElement, oneElement, less);

  addCommutativity(multiply);
  addAssociativity(multiply);
  addRightIdentity(multiply, oneElement);

  //axiom( X0*zero==zero );
  unsigned mulFun = env.signature->getInterpretingSymbol(multiply);
  TermList x(0,false);
  TermList xMulZero(Term::create2(mulFun, x, zeroElement));
  Literal* xEqXMulZero = Literal::createEquality(true, xMulZero, zeroElement, srt);
  addTheoryUnitClause(xEqXMulZero,EXPENSIVE);

  // Distributivity
  //axiom x*(y+z) = (x*y)+(x*z)

  unsigned plusFun = env.signature->getInterpretingSymbol(plus);
  TermList y(1,false);
  TermList z(2,false);

  TermList yPz(Term::create2(plusFun,y,z));
  TermList xTyPz(Term::create2(mulFun,x,yPz));

  TermList xTy(Term::create2(mulFun,x,y));
  TermList xTz(Term::create2(mulFun,x,z));
  TermList xTyPxTz(Term::create2(plusFun,xTy,xTz));
  
  Literal* distrib = Literal::createEquality(true, xTyPz, xTyPxTz,srt);
  addTheoryUnitClause(distrib, EXPENSIVE);

  // Divisibility
  // (x != 0 & x times z = y & x times w = y) -> z = w
  // x=0 | x*z != y | x*w != y | z=w
  TermList w(3,false);
  Literal* xEz = Literal::createEquality(true,x,zeroElement,srt);
  TermList xTw(Term::create2(mulFun,x,w));
  Literal* xTznEy = Literal::createEquality(false,xTz,y,srt); 
  Literal* xTwnEy = Literal::createEquality(false,xTw,y,srt); 
  Literal* zEw = Literal::createEquality(true,z,w,srt);

  addTheoryNonUnitClause(xEz,xTznEy,xTwnEy,zEw,EXPENSIVE);
  
}

/**
 * Add axioms for integer division
 * Also modulo and abs functions
 */
void TheoryAxioms::addIntegerDivisionWithModuloAxioms(Interpretation plus, Interpretation unaryMinus, Interpretation less,
                                Interpretation multiply, Interpretation divide, Interpretation divides,
                                Interpretation modulo, Interpretation abs, TermList zeroElement,
                                TermList oneElement)
{
  CALL("TheoryAxioms::addIntegerDivisionWithModuloAxioms");


  unsigned srt = theory->getOperationSort(plus);
  ASS_EQ(srt, theory->getOperationSort(unaryMinus));
  ASS_EQ(srt, theory->getOperationSort(less));
  ASS_EQ(srt, theory->getOperationSort(multiply));
  ASS_EQ(srt, theory->getOperationSort(divide));
  ASS_EQ(srt, theory->getOperationSort(divides));
  ASS_EQ(srt, theory->getOperationSort(modulo));
  ASS_EQ(srt, theory->getOperationSort(abs));

  unsigned lessPred = env.signature->getInterpretingSymbol(less);
  unsigned umFun = env.signature->getInterpretingSymbol(unaryMinus);
  unsigned mulFun = env.signature->getInterpretingSymbol(multiply);
  unsigned divFun = env.signature->getInterpretingSymbol(divide);
  unsigned modFun = env.signature->getInterpretingSymbol(modulo);
  unsigned absFun = env.signature->getInterpretingSymbol(abs);
  unsigned plusFun = env.signature->getInterpretingSymbol(plus);

  addIntegerAbsAxioms(abs,less,unaryMinus,zeroElement);

  TermList x(1,false);
  TermList y(2,false);

  // divides
  //TODO

  Literal* yis0 = Literal::createEquality(true,y,zeroElement,srt);
  TermList modxy(Term::create2(modFun,x,y));

  //y!=0 => x = modulo(x,y) +  multiply(y,div(x,y))

  TermList divxy(Term::create2(divFun,x,y));
  TermList mulydivxy(Term::create2(mulFun,y,divxy));
  TermList sum(Term::create2(plusFun,modxy,mulydivxy));
  Literal* xeqsum = Literal::createEquality(true,x,sum,srt);
  addTheoryNonUnitClause(yis0,xeqsum,EXPENSIVE);

  // y!=0 => (0 <= mod(x,y))
  // y=0 | ~(mod(x,y) < 0)
  Literal* modxyge0 = Literal::create2(lessPred,false,modxy,zeroElement);
  addTheoryNonUnitClause(yis0,modxyge0,EXPENSIVE);

  // y!=0 => (mod(x,y) <= abs(y)-1)
  // y=0 | ~( abs(y)-1 < mod(x,y) )
  TermList absy(Term::create1(absFun,y));
  TermList m1(Term::create1(umFun,oneElement));
  TermList absym1(Term::create2(plusFun,absy,m1));
  Literal* modxyleabsym1 = Literal::create2(lessPred,false,absym1,modxy);
  addTheoryNonUnitClause(yis0,modxyleabsym1,EXPENSIVE);

}

void TheoryAxioms::addIntegerDividesAxioms(Interpretation divides, Interpretation multiply, TermList zero, TermList n)
{
  CALL("TheoryAxioms::addIntegerDividesAxioms");

#if VDEBUG
  // ASSERT n>0
  ASS(theory->isInterpretedConstant(n)); 
  IntegerConstantType nc;
  ALWAYS(theory->tryInterpretConstant(n,nc));
  ASS(nc.toInner()>0);
#endif

// ![Y] : (divides(n,Y) <=> ?[Z] : multiply(Z,n) = Y)

  unsigned srt = theory->getOperationSort(divides);
  ASS_EQ(srt, theory->getOperationSort(multiply));

  unsigned divsPred = env.signature->getInterpretingSymbol(divides);
  unsigned mulFun   = env.signature->getInterpretingSymbol(multiply);

  TermList y(1,false);
  TermList z(2,false);

// divides(n,Y) | multiply(Z,n) != Y 
  Literal* divsXY = Literal::create2(divsPred,true,n,y);
  TermList mZX(Term::create2(mulFun,z,n));
  Literal* mZXneY = Literal::createEquality(false,mZX,y,srt);
  addTheoryNonUnitClause(divsXY,mZXneY,EXPENSIVE);

// ~divides(n,Y) | multiply(skolem(n,Y),n)=Y
  Literal* ndivsXY = Literal::create2(divsPred,false,n,y);
  
  // create a skolem function with signature srt*srt>srt
  unsigned skolem = env.signature->addSkolemFunction(2);
  Signature::Symbol* sym = env.signature->getFunction(skolem);
  sym->setType(OperatorType::getFunctionType({srt,srt},srt));
  TermList skXY(Term::create2(skolem,n,y));
  TermList msxX(Term::create2(mulFun,skXY,n));
  Literal* msxXeqY = Literal::createEquality(true,msxX,y,srt);

  addTheoryNonUnitClause(ndivsXY,msxXeqY,EXPENSIVE);

}

void TheoryAxioms::addIntegerAbsAxioms(Interpretation abs, Interpretation less, 
                                       Interpretation unaryMinus, TermList zeroElement)
{
  CALL("TheoryAxioms::addIntegerAbsAxioms");

  unsigned srt = theory->getOperationSort(abs);
  ASS_EQ(srt, theory->getOperationSort(less));
  ASS_EQ(srt, theory->getOperationSort(unaryMinus));

  unsigned lessPred = env.signature->getInterpretingSymbol(less);
  unsigned absFun = env.signature->getInterpretingSymbol(abs);
  unsigned umFun = env.signature->getInterpretingSymbol(unaryMinus);

  TermList x(1,false);
  TermList absX(Term::create1(absFun,x));
  TermList mx(Term::create1(umFun,x));
  TermList absmX(Term::create1(absFun,mx));

  // If x is positive then abs(x)=x 
  // If x is negative then abs(x)=-x 

  Literal* xNeg = Literal::create2(lessPred,false,zeroElement,x); // not 0<x
  Literal* xPos = Literal::create2(lessPred,false,x,zeroElement); // not x<0

  Literal* absXeqX = Literal::createEquality(true,absX,x,srt);
  Literal* absXeqmX = Literal::createEquality(true,absX,mx,srt);

  addTheoryNonUnitClause(xNeg,absXeqX,EXPENSIVE);
  addTheoryNonUnitClause(xPos,absXeqmX,EXPENSIVE);

}


/**
 * Add axioms for quotient i.e. rat or real division 
 */
void TheoryAxioms::addQuotientAxioms(Interpretation quotient, Interpretation multiply,
    TermList zeroElement, TermList oneElement, Interpretation less)
{
  CALL("TheoryAxioms::addQuotientAxioms");

  unsigned srt = theory->getOperationSort(quotient);
  ASS_EQ(srt, theory->getOperationSort(multiply));
  ASS_EQ(srt, theory->getOperationSort(less));

  TermList x(1,false);
  TermList y(2,false);

  unsigned mulFun = env.signature->getInterpretingSymbol(multiply);
  unsigned divFun = env.signature->getInterpretingSymbol(quotient);

  Literal* guardx = Literal::createEquality(true,x,zeroElement,srt); 

  // x=0 | quotient(x,x)=1, easily derivable!
  //TermList qXX(Term::create2(quotient,x,x));
  //Literal* xQxis1 = Literal::createEquality(true,qXX,oneElement,srt);
  //addTheoryNonUnitClause(guardx,xQxis1);

  // x=0 | quotient(1,x)!=0
  TermList q1X(Term::create2(divFun,oneElement,x));
  Literal* oQxnot0 = Literal::createEquality(false,q1X,zeroElement,srt);
  addTheoryNonUnitClause(guardx,oQxnot0,EXPENSIVE);

  // quotient(x,1)=x, easily derivable!
  //TermList qX1(Term::create2(quotient,x,oneElement));
  //Literal* qx1isx = Literal::createEquality(true,qX1,x,srt);
  //addTheoryUnitClause(qx1isx);

  // x=0 | quotient(multiply(y,x),x)=y
  TermList myx(Term::create2(mulFun,y,x));
  TermList qmx(Term::create2(divFun,myx,x));
  Literal* qmxisy = Literal::createEquality(true,qmx,y,srt);
  addTheoryNonUnitClause(guardx,qmxisy,EXPENSIVE);


}

/**
 * Add axiom valid only for integer ordering: Y>X ->  Y => X+1 
 *
 * ~(x<y) | ~(y,x+1)
 */
void TheoryAxioms::addExtraIntegerOrderingAxiom(Interpretation plus, TermList oneElement,
                                                Interpretation less)
{
  CALL("TheoryAxioms::addExtraIntegerOrderingAxiom");

  unsigned lessPred = env.signature->getInterpretingSymbol(less);
  unsigned plusFun = env.signature->getInterpretingSymbol(plus);
  TermList x(0,false);
  TermList y(1,false);
  Literal* nxLy = Literal::create2(lessPred, false, x, y);
  TermList xPOne(Term::create2(plusFun, x, oneElement));
  Literal* nyLxPOne = Literal::create2(lessPred, false, y,xPOne);
  addTheoryNonUnitClause(nxLy, nyLxPOne,EXPENSIVE);
}
    
/**
 * Add axioms defining floor function
 * @author Giles
 */
void TheoryAxioms::addFloorAxioms(Interpretation floor, Interpretation less, Interpretation unaryMinus,
     Interpretation plus, TermList oneElement)
{
  CALL("TheoryAxioms::addFloorAxioms");

  unsigned lessPred = env.signature->getInterpretingSymbol(less);
  unsigned plusFun = env.signature->getInterpretingSymbol(plus);
  unsigned umFun = env.signature->getInterpretingSymbol(unaryMinus);
  unsigned floorFun = env.signature->getInterpretingSymbol(floor);
  TermList x(0,false);
  TermList floorX(Term::create1(floorFun,x));

  //axiom( floor(X) <= X )
  // is ~(X < floor(X))
  Literal* a1 = Literal::create2(lessPred, false, x, floorX);
  addTheoryUnitClause(a1,EXPENSIVE);

  //axiom( X-1 < floor(X) ) 
  TermList m1(Term::create1(umFun,oneElement));
  TermList xm1(Term::create2(plusFun, x, m1));
  Literal* a2 = Literal::create2(lessPred,true, xm1, floorX);
  addTheoryUnitClause(a2, EXPENSIVE);
} //addFloorAxioms

/**
 * Add axioms defining ceiling function
 * @author Giles
 */ 
void TheoryAxioms::addCeilingAxioms(Interpretation ceiling, Interpretation less, 
     Interpretation plus, TermList oneElement)
{
  CALL("TheoryAxioms::addCeilingAxioms");

  unsigned lessPred = env.signature->getInterpretingSymbol(less);
  unsigned plusFun = env.signature->getInterpretingSymbol(plus);
  unsigned ceilingFun = env.signature->getInterpretingSymbol(ceiling);
  TermList x(0,false);
  TermList ceilingX(Term::create1(ceilingFun,x));

  //axiom( ceiling(X) >= X ) 
  // is ~( ceiling(X) < X )
  Literal* a1 = Literal::create2(lessPred, false, ceilingX, x);
  addTheoryUnitClause(a1,EXPENSIVE);

  //axiom( ceiling(X) < X+1 ) 
  TermList xp1(Term::create2(plusFun, x, oneElement));
  Literal* a2 = Literal::create2(lessPred,true, ceilingX, xp1);
  addTheoryUnitClause(a2, EXPENSIVE);
} //addCeilingAxioms

/**
 * Add axioms defining round function
 * @author Giles
 */ 
void TheoryAxioms::addRoundAxioms(Interpretation round, Interpretation floor, Interpretation ceiling)
{
  CALL("TheoryAxioms::addRoundAxioms");
  
  //TODO... not that interesting as $round not in TPTP or translations
  // Suggested axioms:
  // round(x) = floor(x) | round(x) = ceiling(x)
  // x-0.5 > floor(x) => round(x) = ceiling(x)
  // x+0.5 < ceiling(x) => round(x) = floor(x)
  // x-0.5 = floor(x) => ?y : is_int(y) & 2*y = round(x)
  // x+0.5 = ceiling(x) => ?y : is_int(y) & 2*y = round(x)
  //NOT_IMPLEMENTED;

} //addRoundAxioms

/**
 * Add axioms defining truncate function
 * truncate is 'towards zero'
 *
 * >> x positive
 * x<0 | ~( x < tr(x) )		// x-1 < tr(x) <= x 
 * x<0 | x-1 < tr(x) 
 *
 * >> x negative
 * ~(x<0) | ~( tr(x) < x )	// x <= tr(x) < x+1 
 * ~(x<0) | tr(x) < x+1
 *
 * @author Giles
 */ 
void TheoryAxioms::addTruncateAxioms(Interpretation truncate, Interpretation less, Interpretation unaryMinus,
                      Interpretation plus, TermList zeroElement, TermList oneElement)
{
  CALL("TheoryAxioms::addTruncateAxioms");

  unsigned lessPred = env.signature->getInterpretingSymbol(less);
  unsigned plusFun = env.signature->getInterpretingSymbol(plus);
  unsigned umFun = env.signature->getInterpretingSymbol(unaryMinus);
  unsigned truncateFun = env.signature->getInterpretingSymbol(truncate);
  TermList x(0,false);
  TermList truncateX(Term::create1(truncateFun,x));

  TermList m1(Term::create1(umFun,oneElement));
  TermList xm1(Term::create2(plusFun,x,m1));
  TermList xp1(Term::create2(plusFun,x,oneElement));

  Literal* xLz = Literal::create2(lessPred,true,x,zeroElement);
  Literal* nxLz= Literal::create2(lessPred,false,x,zeroElement);

  //x<0 | ~( x < tr(x) )
  Literal* a1 = Literal::create2(lessPred,false,x,truncateX);
  addTheoryNonUnitClause(xLz,a1,EXPENSIVE);

  //x<0 | x-1 < tr(x)
  Literal* a2 = Literal::create2(lessPred,true,xm1,truncateX);
  addTheoryNonUnitClause(xLz,a2,EXPENSIVE);

  // ~(x<0) | ~( tr(x) < x )
  Literal* a3 = Literal::create2(lessPred,false,truncateX,x);
  addTheoryNonUnitClause(nxLz,a3,EXPENSIVE);

  // ~(x<0) | tr(x) < x+1
  Literal* a4 = Literal::create2(lessPred,true,truncateX,xp1);
  addTheoryNonUnitClause(nxLz,a4,EXPENSIVE);

} //addTruncateAxioms

/**
 * Adds the extensionality axiom of arrays (of type array1 or array2): 
 * select(X,sk(X,Y)) != select(Y,sk(X,Y)) | X = Y
 *
 * @author Laura Kovacs
 * @since 31/08/2012, Vienna
 * @since 11/11/2013 Manchester, updates
 * @author Andrei Voronkov
 * @since 05/01/2014 Vienna, add axiom in clause form (we need skolem function in other places)
 * @author Bernhard Kragl
*/
void TheoryAxioms::addArrayExtensionalityAxioms(unsigned arraySort, unsigned skolemFn)
{
  CALL("TheoryAxioms::addArrayExtenstionalityAxioms");

  unsigned sel = env.signature->getInterpretingSymbol(Theory::ARRAY_SELECT,Theory::getArrayOperatorType(arraySort,Theory::ARRAY_SELECT));

  Sorts::ArraySort* si = env.sorts->getArraySort(arraySort);
  unsigned rangeSort = si->getInnerSort();

  TermList x(0,false);
  TermList y(1,false);
  
  TermList sk(Term::create2(skolemFn, x, y)); //sk(x,y)
  TermList sel_x_sk(Term::create2(sel,x,sk)); //select(x,sk(x,y))
  TermList sel_y_sk(Term::create2(sel,y,sk)); //select(y,sk(x,y))
  Literal* eq = Literal::createEquality(true,x,y,arraySort); //x = y
  Literal* ineq = Literal::createEquality(false,sel_x_sk,sel_y_sk,rangeSort); //select(x,sk(x,y) != select(y,z)
  
  addTheoryNonUnitClause(eq, ineq,CHEAP);
} // addArrayExtensionalityAxiom    

/**
 * Adds the extensionality axiom of boolean arrays:
 * select(X, sk(X, Y)) <~> select(Y, sk(X, Y)) | X = Y
 *
 * @since 25/08/2015 Gothenburg
 * @author Evgeny Kotelnikov
 */
void TheoryAxioms::addBooleanArrayExtensionalityAxioms(unsigned arraySort, unsigned skolemFn)
{
  CALL("TheoryAxioms::addBooleanArrayExtenstionalityAxioms");

  OperatorType* selectType = Theory::getArrayOperatorType(arraySort,Theory::ARRAY_BOOL_SELECT);

  unsigned sel = env.signature->getInterpretingSymbol(Theory::ARRAY_BOOL_SELECT,selectType);

  TermList x(0,false);
  TermList y(1,false);

  TermList sk(Term::create2(skolemFn, x, y)); //sk(x,y)
  Formula* x_neq_y = new AtomicFormula(Literal::createEquality(false,x,y,arraySort)); //x != y

  Formula* sel_x_sk = new AtomicFormula(Literal::create2(sel, true, x, sk)); //select(x,sk(x,y))
  Formula* sel_y_sk = new AtomicFormula(Literal::create2(sel, true, y, sk)); //select(y,sk(x,y))
  Formula* sx_neq_sy = new BinaryFormula(XOR, sel_x_sk, sel_y_sk); //select(x,sk(x,y)) <~> select(y,sk(x,y))

  Formula* axiom = new QuantifiedFormula(FORALL, new Formula::VarList(0, new Formula::VarList(1, 0)),
                                         new Formula::SortList(arraySort, new Formula::SortList(arraySort,0)),
                                         new BinaryFormula(IMP, x_neq_y, sx_neq_sy));

  addAndOutputTheoryUnit(new FormulaUnit(axiom, new Inference(Inference::THEORY_AXIOM), Unit::AXIOM),CHEAP);
} // addBooleanArrayExtensionalityAxiom

/**
* Adds the write/select axiom of arrays (of type array1 or array2), 
 * @author Laura Kovacs
 * @since 31/08/2012, Vienna
*/
void TheoryAxioms::addArrayWriteAxioms(unsigned arraySort)
{
  CALL("TheoryAxioms::addArrayWriteAxioms");
        
  unsigned func_select = env.signature->getInterpretingSymbol(Theory::ARRAY_SELECT,Theory::getArrayOperatorType(arraySort,Theory::ARRAY_SELECT));
  unsigned func_store = env.signature->getInterpretingSymbol(Theory::ARRAY_STORE,Theory::getArrayOperatorType(arraySort,Theory::ARRAY_STORE));

  Sorts::ArraySort* si = env.sorts->getArraySort(arraySort);
  unsigned rangeSort = si->getInnerSort();
  unsigned domainSort = si->getIndexSort();

  TermList i(0,false);
  TermList j(1,false);
  TermList v(2,false);
  TermList a(3,false);
  TermList args[] = {a, i, v};
        
  //axiom (!A: arraySort, !I:domainSort, !V:rangeSort: (select(store(A,I,V), I) = V
  TermList wAIV(Term::create(func_store, 3, args)); //store(A,I,V)
  TermList sWI(Term::create2(func_select, wAIV,i)); //select(wAIV,I)
  Literal* ax = Literal::createEquality(true, sWI, v, rangeSort);
  addTheoryUnitClause(ax,CHEAP);

  //axiom (!A: arraySort, !I,J:domainSort, !V:rangeSort: (I!=J)->(select(store(A,I,V), J) = select(A,J)
  TermList sWJ(Term::create2(func_select, wAIV,j)); //select(wAIV,J)
  TermList sAJ(Term::create2(func_select, a, j)); //select(A,J)
        
  Literal* indexEq = Literal::createEquality(true, i, j, domainSort);//!(!(I=J)) === I=J
  Literal* writeEq = Literal::createEquality(true, sWJ, sAJ, rangeSort);//(select(store(A,I,V), J) = select(A,J)
  addTheoryNonUnitClause(indexEq, writeEq,CHEAP);
} //

/**
* Adds the write/select axiom of arrays (of type array1 or array2),
 * @author Laura Kovacs
 * @since 31/08/2012, Vienna
*/
void TheoryAxioms::addBooleanArrayWriteAxioms(unsigned arraySort)
{
  CALL("TheoryAxioms::addArrayWriteAxioms");

  unsigned pred_select = env.signature->getInterpretingSymbol(Theory::ARRAY_BOOL_SELECT,Theory::getArrayOperatorType(arraySort,Theory::ARRAY_BOOL_SELECT));
  unsigned func_store = env.signature->getInterpretingSymbol(Theory::ARRAY_STORE,Theory::getArrayOperatorType(arraySort,Theory::ARRAY_STORE));

  Sorts::ArraySort* si = env.sorts->getArraySort(arraySort);
  unsigned domainSort = si->getIndexSort();

  TermList a(0,false);
  TermList i(1,false);

  TermList false_(Term::foolFalse());
  TermList true_(Term::foolTrue());

  // select(store(A,I,$$true), I)
  //~select(store(A,I,$$false), I)

  for (TermList bval : {false_,true_}) {
    TermList args[] = {a, i, bval};
    TermList wAIV(Term::create(func_store, 3, args)); //store(A,I,bval)
    Literal* lit = Literal::create2(pred_select, true, wAIV,i);
    if (bval == false_) {
      lit = Literal::complementaryLiteral(lit);
    }
    Formula* ax = new AtomicFormula(lit);
    addAndOutputTheoryUnit(new FormulaUnit(ax, new Inference(Inference::THEORY_AXIOM), Unit::AXIOM),CHEAP);
  }

  TermList v(2,false);
  TermList j(3,false);

  TermList args[] = {a, i, v};

  //axiom (!A: arraySort, !I,J:domainSort, !V:rangeSort: (I!=J)->(select(store(A,I,V), J) <=> select(A,J)
  TermList wAIV(Term::create(func_store, 3, args)); //store(A,I,V)
  Formula* sWJ = new AtomicFormula(Literal::create2(pred_select, true, wAIV,j)); //select(wAIV,J)
  Formula* sAJ = new AtomicFormula(Literal::create2(pred_select, true, a, j)); //select(A,J)

  Formula* indexEq = new AtomicFormula(Literal::createEquality(false, i, j, domainSort));//I!=J
  Formula* writeEq = new BinaryFormula(IFF, sWJ, sAJ);//(select(store(A,I,V), J) <=> select(A,J)
  Formula* ax2 = new BinaryFormula(IMP, indexEq, writeEq);
  addAndOutputTheoryUnit(new FormulaUnit(ax2, new Inference(Inference::THEORY_AXIOM), Unit::AXIOM),CHEAP);
} //

//Axioms for integer division that hven't been implemented yet
//
//axiom( (ige(X0,zero) & igt(X1,zero)) --> ( ilt(X0-X1, idiv(X0,X1)*X1) & ile(idiv(X0,X1)*X1, X0) ) );
//axiom( (ilt(X0,zero) & ilt(X1,zero)) --> ( igt(X0-X1, idiv(X0,X1)*X1) & ige(idiv(X0,X1)*X1, X0) ) );
//axiom( (ige(X0,zero) & ilt(X1,zero)) --> ( ilt(X0+X1, idiv(X0,X1)*X1) & ile(idiv(X0,X1)*X1, X0) ) );
//axiom( (ilt(X0,zero) & igt(X1,zero)) --> ( igt(X0+X1, idiv(X0,X1)*X1) & ige(idiv(X0,X1)*X1, X0) ) );
//axiom( (ilt(X0,zero) & igt(X1,zero)) --> ( igt(X0+X1, idiv(X0,X1)*X1) & ige(idiv(X0,X1)*X1, X0) ) );
//axiom( (X1!=zero) --> (idiv(X0,X1)+X2==idiv(X0+(X1*X2),X1)) );


/**
 * Add theory axioms to the @b problem that are relevant to
 * units present in the problem. The problem must have been processed
 * by the InterpretedNormalizer before using this rule
 *
 * @since 11/11/2013, Manchester: bug fixes
 * @author Andrei Voronkov
 */
void TheoryAxioms::apply()
{
  CALL("TheoryAxioms::applyProperty");
  Property* prop = _prb.getProperty();
  bool modified = false;
  bool haveIntPlus =
    prop->hasInterpretedOperation(Theory::INT_PLUS) ||
    prop->hasInterpretedOperation(Theory::INT_UNARY_MINUS) ||
    prop->hasInterpretedOperation(Theory::INT_LESS) ||
    prop->hasInterpretedOperation(Theory::INT_MULTIPLY);
  bool haveIntMultiply =
    prop->hasInterpretedOperation(Theory::INT_MULTIPLY);

  bool haveIntDivision =
    prop->hasInterpretedOperation(Theory::INT_QUOTIENT_E) || // let's ignore the weird _F and _T for now!
    prop->hasInterpretedOperation(Theory::INT_REMAINDER_E) ||
    prop->hasInterpretedOperation(Theory::INT_ABS);

  bool haveIntDivides = prop->hasInterpretedOperation(Theory::INT_DIVIDES);

  bool haveIntFloor = prop->hasInterpretedOperation(Theory::INT_FLOOR);
  bool haveIntCeiling = prop->hasInterpretedOperation(Theory::INT_CEILING);
  bool haveIntRound = prop->hasInterpretedOperation(Theory::INT_ROUND);
  bool haveIntTruncate = prop->hasInterpretedOperation(Theory::INT_TRUNCATE);
  bool haveIntUnaryRoundingFunction = haveIntFloor || haveIntCeiling || haveIntRound || haveIntTruncate;

  if (haveIntPlus || haveIntUnaryRoundingFunction || haveIntDivision || haveIntDivides) {
    TermList zero(theory->representConstant(IntegerConstantType(0)));
    TermList one(theory->representConstant(IntegerConstantType(1)));
    if(haveIntMultiply || haveIntDivision || haveIntDivides) {
      addAdditionOrderingAndMultiplicationAxioms(Theory::INT_PLUS, Theory::INT_UNARY_MINUS, zero, one,
						 Theory::INT_LESS, Theory::INT_MULTIPLY);
      if(haveIntDivision){
        addIntegerDivisionWithModuloAxioms(Theory::INT_PLUS, Theory::INT_UNARY_MINUS, Theory::INT_LESS,
                                 Theory::INT_MULTIPLY, Theory::INT_QUOTIENT_E, Theory::INT_DIVIDES,
                                 Theory::INT_REMAINDER_E, Theory::INT_ABS, zero,one);
      }
      else if(haveIntDivides){ 
        Stack<TermList>& ns = env.signature->getDividesNvalues(); 
        Stack<TermList>::Iterator nsit(ns);
        while(nsit.hasNext()){
          TermList n = nsit.next();
          addIntegerDividesAxioms(Theory::INT_DIVIDES,Theory::INT_MULTIPLY,zero,n); 
        }
      }
    }
    else {
      addAdditionAndOrderingAxioms(Theory::INT_PLUS, Theory::INT_UNARY_MINUS, zero, one,
				   Theory::INT_LESS);
    }
    addExtraIntegerOrderingAxiom(Theory::INT_PLUS, one, Theory::INT_LESS);
    modified = true;
  }
  bool haveRatPlus =
    prop->hasInterpretedOperation(Theory::RAT_PLUS) ||
    prop->hasInterpretedOperation(Theory::RAT_UNARY_MINUS) ||
    prop->hasInterpretedOperation(Theory::RAT_LESS) ||
    prop->hasInterpretedOperation(Theory::RAT_QUOTIENT) ||
    prop->hasInterpretedOperation(Theory::RAT_MULTIPLY);
  bool haveRatMultiply =
    prop->hasInterpretedOperation(Theory::RAT_MULTIPLY);
  bool haveRatQuotient =
    prop->hasInterpretedOperation(Theory::RAT_QUOTIENT);

  bool haveRatFloor = prop->hasInterpretedOperation(Theory::RAT_FLOOR);
  bool haveRatCeiling = prop->hasInterpretedOperation(Theory::RAT_CEILING);
  bool haveRatRound = prop->hasInterpretedOperation(Theory::RAT_ROUND);
  bool haveRatTruncate = prop->hasInterpretedOperation(Theory::RAT_TRUNCATE);
  bool haveRatUnaryRoundingFunction = haveRatFloor || haveRatCeiling || haveRatRound || haveRatTruncate;

  if (haveRatPlus || haveRatUnaryRoundingFunction) {
    TermList zero(theory->representConstant(RationalConstantType(0, 1)));
    TermList one(theory->representConstant(RationalConstantType(1, 1)));
    if(haveRatMultiply || haveRatRound || haveRatQuotient) {
      addAdditionOrderingAndMultiplicationAxioms(Theory::RAT_PLUS, Theory::RAT_UNARY_MINUS, zero, one,
						 Theory::RAT_LESS, Theory::RAT_MULTIPLY);

      if(haveRatQuotient){
        addQuotientAxioms(Theory::RAT_QUOTIENT,Theory::RAT_MULTIPLY,zero,one,Theory::RAT_LESS);
      }
    }
    else {
      addAdditionAndOrderingAxioms(Theory::RAT_PLUS, Theory::RAT_UNARY_MINUS, zero, one,
				   Theory::RAT_LESS);
    }
    if(haveRatFloor || haveRatRound){
      addFloorAxioms(Theory::RAT_FLOOR,Theory::RAT_LESS,Theory::RAT_UNARY_MINUS,Theory::RAT_PLUS,one);
    }
    if(haveRatCeiling || haveRatRound){
      addCeilingAxioms(Theory::RAT_CEILING,Theory::RAT_LESS,Theory::RAT_PLUS,one);
    }
    if(haveRatRound){
      //addRoundAxioms(Theory::INT_TRUNCATE,Theory::INT_FLOOR,Theory::INT_CEILING);
    }
    if(haveRatTruncate){
      addTruncateAxioms(Theory::RAT_TRUNCATE,Theory::RAT_LESS,Theory::RAT_UNARY_MINUS,
                        Theory::RAT_PLUS,zero,one);
    }
    modified = true;
  }
  bool haveRealPlus =
    prop->hasInterpretedOperation(Theory::REAL_PLUS) ||
    prop->hasInterpretedOperation(Theory::REAL_UNARY_MINUS) ||
    prop->hasInterpretedOperation(Theory::REAL_LESS) ||
    prop->hasInterpretedOperation(Theory::REAL_QUOTIENT) ||
    prop->hasInterpretedOperation(Theory::REAL_MULTIPLY);
  bool haveRealMultiply =
    prop->hasInterpretedOperation(Theory::REAL_MULTIPLY);
  bool haveRealQuotient =
    prop->hasInterpretedOperation(Theory::REAL_QUOTIENT);

  bool haveRealFloor = prop->hasInterpretedOperation(Theory::REAL_FLOOR);
  bool haveRealCeiling = prop->hasInterpretedOperation(Theory::REAL_CEILING);
  bool haveRealRound = prop->hasInterpretedOperation(Theory::REAL_ROUND);
  bool haveRealTruncate = prop->hasInterpretedOperation(Theory::REAL_TRUNCATE);
  bool haveRealUnaryRoundingFunction = haveRealFloor || haveRealCeiling || haveRealRound || haveRealTruncate;

  if (haveRealPlus || haveRealUnaryRoundingFunction) {
    TermList zero(theory->representConstant(RealConstantType(RationalConstantType(0, 1))));
    TermList one(theory->representConstant(RealConstantType(RationalConstantType(1, 1))));
    if(haveRealMultiply || haveRealQuotient) {
      addAdditionOrderingAndMultiplicationAxioms(Theory::REAL_PLUS, Theory::REAL_UNARY_MINUS, zero, one,
						 Theory::REAL_LESS, Theory::REAL_MULTIPLY);

      if(haveRealQuotient){
        addQuotientAxioms(Theory::REAL_QUOTIENT,Theory::REAL_MULTIPLY,zero,one,Theory::REAL_LESS);
      }
    }
    else {
      addAdditionAndOrderingAxioms(Theory::REAL_PLUS, Theory::REAL_UNARY_MINUS, zero, one,
				   Theory::REAL_LESS);
    }
    if(haveRealFloor || haveRealRound){
      addFloorAxioms(Theory::REAL_FLOOR,Theory::REAL_LESS,Theory::REAL_UNARY_MINUS,Theory::REAL_PLUS,one);
    }
    if(haveRealCeiling || haveRealRound){
      addCeilingAxioms(Theory::REAL_CEILING,Theory::REAL_LESS,Theory::REAL_PLUS,one);
    }
    if(haveRealRound){
      //addRoundAxioms(Theory::INT_TRUNCATE,Theory::INT_FLOOR,Theory::INT_CEILING);
    }
    if(haveRealTruncate){
      addTruncateAxioms(Theory::REAL_TRUNCATE,Theory::REAL_LESS,Theory::REAL_UNARY_MINUS,
                        Theory::REAL_PLUS,zero,one);
    }

    modified = true;
  }

  VirtualIterator<unsigned> arraySorts = env.sorts->getStructuredSorts(Sorts::StructuredSort::ARRAY);
  while(arraySorts.hasNext()){
    unsigned arraySort = arraySorts.next();

    bool isBool = (env.sorts->getArraySort(arraySort)->getInnerSort() == Sorts::SRT_BOOL);
    
    // Check if they are used
    Interpretation arraySelect = isBool ? Theory::ARRAY_BOOL_SELECT : Theory::ARRAY_SELECT;
    bool haveSelect = prop->hasInterpretedOperation(arraySelect,Theory::getArrayOperatorType(arraySort,arraySelect));
    bool haveStore = prop->hasInterpretedOperation(Theory::ARRAY_STORE,Theory::getArrayOperatorType(arraySort,Theory::ARRAY_STORE));

    if (haveSelect || haveStore) {
      unsigned sk = theory->getArrayExtSkolemFunction(arraySort);
      if (isBool) {
        addBooleanArrayExtensionalityAxioms(arraySort, sk);
      } else {
        addArrayExtensionalityAxioms(arraySort, sk);
      }
      if (haveStore) {
        if (isBool) {
          addBooleanArrayWriteAxioms(arraySort);
        } else {
          addArrayWriteAxioms(arraySort);
        }
      }
      modified = true;
    }
  }

  VirtualIterator<TermAlgebra*> tas = env.signature->termAlgebrasIterator();
  while (tas.hasNext()) {
    TermAlgebra* ta = tas.next();

    addExhaustivenessAxiom(ta);
    // the other axioms can be replaced by the full inference system
    if (env.options->termAlgebraInferences() != Options::TAInferences::FULL) {
      addDistinctnessAxiom(ta);
      addInjectivityAxiom(ta);
      addDiscriminationAxiom(ta);
    }

    if (ta->allowsCyclicTerms()) {
      if (env.options->termAlgebraUniquenessCheck() == Options::TAUniquenessCheck::AXIOM
          || env.options->termAlgebraUniquenessCheck() == Options::TAUniquenessCheck::RULE) {
        addFixpointAxioms(ta);
      }
    } else {
      if (env.options->termAlgebraCyclicityCheck() == Options::TACyclicityCheck::AXIOM
          || env.options->termAlgebraCyclicityCheck() == Options::TACyclicityCheck::RULE) {
        addAcyclicityAxioms(ta);
      }
    }

    modified = true;
  }

  if(modified) {
    _prb.reportEqualityAdded(false);
  }
} // TheoryAxioms::apply

void TheoryAxioms::applyFOOL() {
  CALL("TheoryAxioms::applyFOOL");

  TermList t(Term::foolTrue());
  TermList f(Term::foolFalse());

  Inference* foolAxiom = new Inference(Inference::FOOL_AXIOM);

  // Add "$$true != $$false"
  Clause* tneqfClause = new(1) Clause(1, Unit::AXIOM, foolAxiom);
  (*tneqfClause)[0] = Literal::createEquality(false, t, f, Sorts::SRT_BOOL);
  addAndOutputTheoryUnit(tneqfClause, CHEAP);

  // Do not add the finite domain axiom if --fool_paradomulation on
  if (env.options->FOOLParamodulation()) {
    return;
  }

  // Add "![X : $bool]: ((X = $$true) | (X = $$false))"
  Clause* boolVarClause = new(2) Clause(2, Unit::AXIOM, foolAxiom);
  (*boolVarClause)[0] = Literal::createEquality(true, TermList(0, false), t, Sorts::SRT_BOOL);
  (*boolVarClause)[1] = Literal::createEquality(true, TermList(0, false), f, Sorts::SRT_BOOL);
  addAndOutputTheoryUnit(boolVarClause, CHEAP);
} // TheoryAxioms::addBooleanDomainAxiom

/*
 * Note: In contrast to all other internally added theory axioms, the exhaustiveness axiom is
 * added in some cases as Formula and not as a clause. We would like to enforce the invariant that all internally
 * added theory axioms are added as clauses, in order to allow for an easy check whether a clause is
 * a theory axiom or not (without going up the preprocessing derivation until we derive at the axiom formula).
 * We currently already use this easy check, and miss the exhaustiveness axiom in some cases.
 *
 * Adding the exhaustiveness axiom as clause is difficult in the case where some destructor 
 * has boolean sort: The currently implemented clausification-algorithms (default and newcnf) differ
 * in how they clausify the axiom formula, and newcnf as far as I know generates different clausifications
 * of the exhaustiveness axiom formula depending on the value of some magic constants.
 */
void TheoryAxioms::addExhaustivenessAxiom(TermAlgebra* ta) {
  CALL("TheoryAxioms::addExhaustivenessAxiom");

  TermList x(0, false);

  // Part 1: compute list of literals and set flag if a FOOL-destructor occurs
  Stack<Literal*> lits;
  bool addsFOOL = false;

  Stack<TermList> argTerms;
  for (unsigned i = 0; i < ta->nConstructors(); i++) {
    TermAlgebraConstructor *c = ta->constructor(i);
    argTerms.reset();

    for (unsigned j = 0; j < c->arity(); j++) {
      if (c->argSort(j) == Sorts::SRT_BOOL) {
        addsFOOL = true;
        Literal* lit = Literal::create1(c->destructorFunctor(j), true, x);
        Term* t = Term::createFormula(new AtomicFormula(lit));
        argTerms.push(TermList(t));
      } else {
        Term* t = Term::create1(c->destructorFunctor(j), x);
        argTerms.push(TermList(t));
      }
    }

    TermList rhs(Term::create(c->functor(), argTerms.size(), argTerms.begin()));
    lits.push(Literal::createEquality(true, x, rhs, ta->sort()));
  }
  ASS(!lits.isEmpty());

  // Part 2: add axiom
  // - if no FOOL-destructors occur, add the axiom as clause
  // - otherwise, add the axiom as formula (cf. comments at the beginning of this method)
  Unit* axiom;
  if (!addsFOOL) {
    axiom = Clause::fromStack(lits, Unit::AXIOM, new Inference(Inference::TERM_ALGEBRA_EXHAUSTIVENESS_AXIOM));
  } else {
    Formula* disjunction;
    if(lits.size() == 1) {
        disjunction = new AtomicFormula(lits[0]);
    } else {
      FormulaList* fl = FormulaList::empty();
      for (unsigned i = 0; i < lits.size(); i++)
      {
        FormulaList::push(new AtomicFormula(lits[i]), fl);
      }
      disjunction = new JunctionFormula(Connective::OR, fl);
    }
    Formula::VarList* vars = Formula::VarList::cons(x.var(), Formula::VarList::empty());
    Formula::SortList* sorts = Formula::SortList::cons(ta->sort(), Formula::SortList::empty());
    auto universal = new QuantifiedFormula(Connective::FORALL, vars, sorts, disjunction);

    axiom = new FormulaUnit(universal, new Inference(Inference::TERM_ALGEBRA_EXHAUSTIVENESS_AXIOM), Unit::AXIOM);

    _prb.reportFOOLAdded();
  }

  addAndOutputTheoryUnit(axiom, CHEAP);
}

void TheoryAxioms::addDistinctnessAxiom(TermAlgebra* ta) {
  CALL("TermAlgebra::addDistinctnessAxiom");

  Array<TermList> terms(ta->nConstructors());

  unsigned var = 0;
  for (unsigned i = 0; i < ta->nConstructors(); i++) {
    TermAlgebraConstructor* c = ta->constructor(i);

    Stack<TermList> args;
    for (unsigned j = 0; j < c->arity(); j++) {
      args.push(TermList(var++, false));
    }
    TermList term(Term::create(c->functor(), args.size(), args.begin()));
    terms[i] = term;
  }

  for (unsigned i = 0; i < ta->nConstructors(); i++) {
    for (unsigned j = i + 1; j < ta->nConstructors(); j++) {
      Literal* ineq = Literal::createEquality(false, terms[i], terms[j], ta->sort());
      addTheoryUnitClause(ineq, new Inference(Inference::TERM_ALGEBRA_DISTINCTNESS_AXIOM),CHEAP);
    }
  }
}

void TheoryAxioms::addInjectivityAxiom(TermAlgebra* ta)
{
  CALL("TheoryAxioms::addInjectivityAxiom");

  for (unsigned i = 0; i < ta->nConstructors(); i++) {
    TermAlgebraConstructor* c = ta->constructor(i);

    Stack<TermList> lhsArgs(c->arity());
    Stack<TermList> rhsArgs(c->arity());

    for (unsigned j = 0; j < c->arity(); j++) {
      lhsArgs.push(TermList(j * 2, false));
      rhsArgs.push(TermList(j * 2 + 1, false));
    }

    TermList lhs(Term::create(c->functor(), lhsArgs.size(), lhsArgs.begin()));
    TermList rhs(Term::create(c->functor(), rhsArgs.size(), rhsArgs.begin()));
    Literal* eql = Literal::createEquality(false, lhs, rhs, ta->sort());

    for (unsigned j = 0; j < c->arity(); j++) {
      Literal* eqr = Literal::createEquality(true, TermList(j * 2, false), TermList(j * 2 + 1, false), c->argSort(j));

      Clause* injectivity = new(2) Clause(2, Unit::AXIOM, new Inference(Inference::TERM_ALGEBRA_INJECTIVITY_AXIOM));
      (*injectivity)[0] = eql;
      (*injectivity)[1] = eqr;
      addAndOutputTheoryUnit(injectivity,CHEAP);
    }
  }
}

void TheoryAxioms::addDiscriminationAxiom(TermAlgebra* ta) {
  CALL("addDiscriminationAxiom");

  Array<TermList> cases(ta->nConstructors());
  for (unsigned i = 0; i < ta->nConstructors(); i++) {
    TermAlgebraConstructor* c = ta->constructor(i);

    Stack<TermList> variables;
    for (unsigned var = 0; var < c->arity(); var++) {
      variables.push(TermList(var, false));
    }

    TermList term(Term::create(c->functor(), variables.size(), variables.begin()));
    cases[i] = term;
  }

  for (unsigned i = 0; i < ta->nConstructors(); i++) {
    TermAlgebraConstructor* constructor = ta->constructor(i);

    if (!constructor->hasDiscriminator()) continue;

    for (unsigned c = 0; c < cases.size(); c++) {
      Literal* lit = Literal::create1(constructor->discriminator(), c == i, cases[c]);
      addTheoryUnitClause(lit, new Inference(Inference::TERM_ALGEBRA_DISCRIMINATION_AXIOM),CHEAP);
    }
  }
}

void TheoryAxioms::addAcyclicityAxioms(TermAlgebra* ta)
{
  CALL("TheoryAxioms::addAcyclicityAxioms");
  ASS(!ta->allowsCyclicTerms())

  // nothing to do if the type is not recursive
  if (!ta->isMutualType(ta))
    return;

  // term algebras/datatypes : no cyclic terms
  // axiomatized with subterm predicate
  for (unsigned i = 0; i < ta->nConstructors(); i++) {
    addSubtermDefinitions(ta, ta->constructor(i));
  }
  addSubtermReflexivity(ta);
}

void TheoryAxioms::addFixpointAxioms(TermAlgebra* ta)
{
  CALL("TheoryAxioms::addFixpointAxioms");
  ASS(ta->allowsCyclicTerms())

  // nothing to do if the type is not recursive
  if (!ta->isMutualType(ta))
    return;

  if (ta->allowsCyclicTerms()) {
    // infinite trees/co-datatypes : cyclic terms exists and are unique
    // axiomatized with subst function
    for (unsigned i = 0; i < ta->nConstructors(); i++) {
      addConstructorCtxDefinitions(ta, ta->constructor(i));
    }
    addCtxFunctionDefinitions(ta);
  }
}

void TheoryAxioms::addSubtermDefinitions(TermAlgebra* ta, TermAlgebraConstructor* c)
{
  CALL("TheoryAxioms::addSubtermDefinitions");

  TermList z(c->arity(), false);

  Stack<TermList> args;
  for (unsigned i = 0; i < c->arity(); i++) {
    args.push(TermList(i, false));
  }
  TermList right(Term::create(c->functor(), args.size(), args.begin()));

  for (unsigned i = 0; i < c->arity(); i++) {
    if (!env.signature->isTermAlgebraSort(c->argSort(i))) continue;

    TermAlgebra* ta2 = env.signature->getTermAlgebraOfSort(c->argSort(i));

    if (!ta->isMutualType(ta2)) continue;

    TermList y(i, false);

    if (env.options->termAlgebraCyclicityCheck() != Options::TACyclicityCheck::RULE) {
      // Direct subterms cannot be subterm subterms: ~Sub(c(x1, ... y ..., xn), y)
      Literal* sub = Literal::create2(ta2->getSubtermPredicate(ta), false, right, y);
      addTheoryUnitClause(sub, new Inference(Inference::TERM_ALGEBRA_ACYCLICITY_AXIOM),CHEAP);
    }

    // Transitivity of the subterm relation: Sub(z, y) -> Sub(z, c(x1, ... y , xn))
    // one axiom for every mutual type (type of z)
    VirtualIterator<TermAlgebra*> tas = env.signature->termAlgebrasIterator();
    while (tas.hasNext()) {
      TermAlgebra* ta3 = tas.next();
      if (ta->isMutualType(ta3)) {
        Clause* transitivity = new(2) Clause(2, Unit::AXIOM, new Inference(Inference::TERM_ALGEBRA_ACYCLICITY_AXIOM));
        (*transitivity)[0] = Literal::create2(ta2->getSubtermPredicate(ta3), false, z, y);
        (*transitivity)[1] = Literal::create2(ta->getSubtermPredicate(ta3), true,  z, right);
        addAndOutputTheoryUnit(transitivity, CHEAP);
      }
    }
  }
}

void TheoryAxioms::addSubtermReflexivity(TermAlgebra* ta) {
  CALL("TheoryAxioms::addSubtermReflexivity");

  TermList x(0, false);
  Literal* sub = Literal::create2(ta->getSubtermPredicate(ta), true, x, x);
  addTheoryUnitClause(sub, new Inference(Inference::TERM_ALGEBRA_ACYCLICITY_AXIOM), CHEAP);
}

void TheoryAxioms::addCtxFunctionDefinitions(TermAlgebra* ta)
{
  CALL("TheoryAxioms::addCtxFunctionDefinitions");

  // cyc(x) = app(x, cyc(x))
  TermList x(0, false);
  TermList cycx(Term::create1(ta->getCycleFunction(), x));
  Literal* l = Literal::createEquality(true,
                                       cycx,
                                       TermList(Term::create2(ta->getAppFunction(ta),
                                                              x,
                                                              cycx)),
                                       ta->sort());

  addTheoryUnitClause(l, new Inference(Inference::TERM_ALGEBRA_CYCLES_AXIOM), CHEAP);
  
  // app(cst(x), y) = x for each mutual type
  TermList y(1, false);
  Lib::VirtualIterator<TermAlgebra*> it = ta->mutualTypes();
  while (it.hasNext()) {
    TermAlgebra *tah = it.next();
    TermList cstx(Term::create1(ta->getCstFunction(tah), x));
    l = Literal::createEquality(true,
                                x,
                                TermList(Term::create2(ta->getAppFunction(tah),
                                                       cstx,
                                                       y)),
                                ta->sort());
  
    addTheoryUnitClause(l, new Inference(Inference::TERM_ALGEBRA_CYCLES), CHEAP);
  }

  // app(hole, x) = x
  TermList hole(Term::createConstant(ta->getHoleConstant()));
  l = Literal::createEquality(true,
                              x,
                              TermList(Term::create2(ta->getAppFunction(ta),
                                                     hole,
                                                     x)),
                              ta->sort());

  addTheoryUnitClause(l, new Inference(Inference::TERM_ALGEBRA_CYCLES), CHEAP);
  
  if (env.options->termAlgebraCyclicityCheck() != Options::TACyclicityCheck::RULE) {
    // hole != cst(x)
    TermList cstx(Term::create1(ta->getCstFunction(ta), x));
    l = Literal::createEquality(false,
                                hole,
                                cstx,
                                ta->contextSort(ta));
  
    addTheoryUnitClause(l, new Inference(Inference::TERM_ALGEBRA_CYCLES), CHEAP);
    
    // unicity
    // x = hole \/ y != app(x, y) \/ z != app(x, z) \/ y = z
    /*
      TermList z(2, false);
      Clause* c = new(4) Clause(4, Unit::AXIOM, new Inference(Inference::TERM_ALGEBRA_CYCLES));
      (*c)[0] = Literal::createEquality(true, x, hole, ta->contextSort(ta));
      (*c)[1] = Literal::createEquality(false,
      y,
      TermList(Term::create2(ta->getAppFunction(ta), x, y)),
      ta->sort());
      (*c)[2] = Literal::createEquality(false,
      z,
      TermList(Term::create2(ta->getAppFunction(ta), x, z)),
      ta->sort());
      (*c)[3] = Literal::createEquality(true, y, z, ta->sort());
  
      addAndOutputTheoryUnit(c, CHEAP);*/

    // TODO compare both versions
    // unicity alternative axiom
    // x = hole \/ y =! app(x, y) \/ y = cyc(x)
    Clause* c = new(3) Clause(3, Unit::AXIOM, new Inference(Inference::TERM_ALGEBRA_CYCLES));
    (*c)[0] = Literal::createEquality(true, x, hole, ta->contextSort(ta));
    (*c)[1] = Literal::createEquality(false,
                                      y,
                                      TermList(Term::create2(ta->getAppFunction(ta), x, y)),
                                      ta->sort());
    (*c)[2] = Literal::createEquality(true, y, cycx, ta->sort());
  
    addAndOutputTheoryUnit(c, CHEAP);
  }
}

void TheoryAxioms::addConstructorCtxDefinitions(TermAlgebra* ta, TermAlgebraConstructor* c)
{
  CALL("TheoryAxioms::addConstructorCtxDefinitions");

  Stack<TermList> args1;
  Stack<TermList> args2;
  Stack<TermList> args3;

  for (unsigned i = 0; i < c->arity(); i++) {
    args1.push(TermList(i, false));
  }
  ASS_EQ(args1.size(), c->arity());

  Literal *l;
  if (env.options->termAlgebraCyclicityCheck() != Options::TACyclicityCheck::RULE) {
      // hole != f_ctx(x1 ... xn)
    l = Literal::createEquality(false,
                                TermList(Term::createConstant(ta->getHoleConstant())),
                                TermList(Term::create(c->getCtxFunction(ta), c->arity(), args1.begin())),
                                ta->contextSort(ta));
    
    addTheoryUnitClause(l, new Inference(Inference::TERM_ALGEBRA_CYCLES), CHEAP);
  }
  
  TermList y(c->arity(), false);
   
  // forall types of holes
  VirtualIterator<TermAlgebra*> it = ta->mutualTypes();
  while (it.hasNext()) {
    TermAlgebra *tah = it.next();
    args2.reset();
    args3.reset();
    
    // app(f_ctx(x1 ... xn), y) = f(x1' ... xn')
    for (unsigned i = 0; i < c->arity(); i++) {
      TermList xi(i, false);
      args3.push(xi);
      if (!env.signature->isTermAlgebraSort(c->argSort(i))) {
        // xi' = xi
        args2.push(xi);
      } else {
        TermAlgebra* tai = env.signature->getTermAlgebraOfSort(c->argSort(i));
        if (tai->isMutualType(tah)) {
          // xi' = app(xi, y)
          args2.push(TermList(Term::create2(tai->getAppFunction(tah),
                                            xi,
                                            y)));
        } else {
          // xi' = xi
          args2.push(xi);
        }        
      }
    }

    ASS_EQ(args2.size(), c->arity());
    ASS_EQ(args3.size(), c->arity());

    l = Literal::createEquality(true,
                                TermList(Term::create2(ta->getAppFunction(tah),
                                                       TermList(Term::create(c->getCtxFunction(tah), c->arity(), args3.begin())),
                                                       y)),
                                TermList(Term::create(c->functor(), c->arity(), args2.begin())),
                                ta->sort());
    addTheoryUnitClause(l, new Inference(Inference::TERM_ALGEBRA_CYCLES_AXIOM), CHEAP);
  }
}
