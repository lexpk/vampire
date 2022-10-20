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
 * @file InductionHelper.hpp
 * Defines class InductionHelper
 *
 */

#ifndef __RapidHelper__
#define __RapidHelper__

#include "Forwards.hpp"

#include "Kernel/Signature.hpp"
#include "Kernel/NumTraits.hpp"

namespace Kernel {

class RapidHelper {
public:
  CLASS_NAME(RapidHelper);
  USE_ALLOCATOR(RapidHelper);

  RapidHelper() {}

  using number = NumTraits<IntegerConstantType>;

  static bool isFinalLoopCount(TermList t);
  static bool isTimePoint(TermList t);

  static bool isRightLimitLiteral(Literal* l);
  static bool isLeftLimitLiteral(Literal* l);  
  
  /** returns true if literal is of the form
   *  a(l#(it1 ... s(itn)), j(l#(it1 ... itn))) = term
   *  where term has certain conditions on its form
   */
  static bool isArrayAccessLit(Literal* l, TermList& itVar, 
    unsigned& termPos, TermStack& arrayAccessesRHS);

  static bool isArrayAccessClause(Clause* c, unsigned& 
    litPos, unsigned& termPos, TermStack& arrayAccessesRHS); 

  /** returns true if literal is of the form
   *  x(l#(it1 ... s(itn)))  =  $sum(x(l#(it1 ... itn)), 1)
   *   or
   *  x(l#(it1 ... s(itn)))  =  $sum(x(l#(it1 ... itn)), $uminus(1))
   */
  static bool isStrongDensityLiteral(Literal* l, TermList& itVar, unsigned& termPos); 
  static bool isStrongDensityClause(Clause* c, unsigned& litPos, unsigned& termPos); 

  /** return true if literal is of the form ~Sub(X, nl#(...))
   */
  static bool isSubLiteral(Literal* l, TermList& itVar); 

  //if literal is a constant of the form Dense-x-l# for some variable x
  //and some time point l#
  static bool isDensityLiteral(Literal* l, unsigned& varFunctor, unsigned& tpFunctor);
  
  /** Returns true if the literal is of the form $less(t1, t2) 
   *  where t1 and t2 are ground. Perhaps update to return true only if
   *  Skolems? 
   */
  static bool maybeDifferentBounds(Literal* l);
  
  /** Returns true if clause c is of the form
   *  malloc(l#(X)) != malloc(l#(Y)) \/ X = Y
   */
  static bool mallocClause(Clause* c);

  /** Returns true if clause c is of the form
   *  struct_field_chain(...) = null
   */
  static bool isChainEqualsNullClause(Clause* c, Term*& chainTerm);
  static bool isChainEqualsValueAt(Clause* c, Term*& chainTerm, Term*& valueTerm);  
  static bool isChainExtensionalityCls(Clause* c);

  /** return true if the literal is of the form 
   *  [~]$less(program-var(l#(sK)), numeral)  
   */
  static bool isSuitableForInduction(Literal* lit, vstring& tpName);

  static TermList intVarAtNextIt(TermList varTerm);
  static TermList intVarAtFirstIt(TermList varTerm);
  static TermList intVarAtLastIt(TermList varTerm, TermList finalLoopCount);        
  static TermList arrAtPrevIt(TermList arrVarTerm);
  static TermList arrAtFirstIt(TermList arrVarTerm);
  static TermList arrAtLastIt(TermList arrVarTerm, TermList finalLoopCount);    
  static TermList changeArrIndex(TermList arr, TermList newIndex); 
  static TermList getFinalCountFromSubLit(Literal* lit);

  static TermList timePointAtNextIt(TermList tp);
  static TermList timePointAtPrevIt(TermList tp);
  static TermList timePointAtFirstIt(TermList tp);
  static TermList timePointAtLastIt(TermList tp, TermList finalLoopCount);

  static bool forceOrder(TermList t1, TermList t2);
  static ArgumentOrderVals forceOrder(Literal* lit);

  static bool increasing(Literal* lit, TermList term);

  static bool isZeroLessThanLit(Literal* lit);

  // returns non-empty option if literal is of the form [~](t < num) or
  // [~](num < t). In either case returns t wrapped in option  
  static Option<TermList> isIntComparisonLit(Literal* lit);

  static bool resolveInequalities(Literal* lit1, Literal* lit2);

  static inline bool isChain(TermList t) {
    if(t.isVar()){ return false; }
    return env.signature->getFunction(t.term()->functor())->chain();
  };

  static inline bool isNull(TermList t) {
    if(t.isVar()){ return false; }
    return env.signature->getFunction(t.term()->functor())->nullPtr();
  };

  static inline bool isObjArray(TermList t) {
    if(t.isVar()){ return false; }
    return env.signature->getFunction(t.term()->functor())->objArray();
  };

  // attempts to decompose t into term +- num if possible
  static tuple<TermList, int> decompose(TermList t);  


private:

  static TermList replaceFinalArg(Term* t, TermList replacement);

  /** returns true if t1 is of the form l#(it1 .... s(itn)) and
    * t2 of the form l#(it1 .... itn)
    */ 
  static bool isTimePointAtNextIter(TermList t1, TermList t2, TermList& itVar);

};

};  // namespace Kernel

#endif /*__InductionHelper__*/