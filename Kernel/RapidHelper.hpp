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

namespace Kernel {

class RapidHelper {
public:
  CLASS_NAME(RapidHelper);
  USE_ALLOCATOR(RapidHelper);

  RapidHelper() {}

  static bool isFinalLoopCount(TermList t);
  static bool isTimePoint(TermList t);

  static bool isRightLimitLiteral(Literal* l);
  static bool isLeftLimitLiteral(Literal* l);  
  
  /** returns true if literal is of the form
   *  a(l#(it1 ... s(itn)), j(l#(it1 ... itn))) = F[ a(l#(it1 ... itn), j(l#(it1 ... itn)))]
   *  for some context F 
   */
  static bool isArrayAccessLit(Literal* l, TermList& itVar, unsigned& termPos);
  static bool isArrayAccessClause(Clause* c, unsigned& litPos, unsigned& termPos); 

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
  static bool isIntegerComparisonLiteral(Literal* l);
  
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


  static bool increasing(Literal* lit, TermList term);
private:

  static TermList replaceFinalArg(Term* t, TermList replacement);

  /** returns true if t1 is of the form l#(it1 .... s(itn)) and
    * t2 of the form l#(it1 .... itn)
    */ 
  static bool isTimePointAtNextIter(TermList t1, TermList t2, TermList& itVar);

};

};  // namespace Kernel

#endif /*__InductionHelper__*/