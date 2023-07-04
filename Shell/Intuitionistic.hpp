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
 * @file Intuitionistic.hpp
 * Defines transformations for expressing intuitionistic semantics.
 */

#ifndef __INTUIT__
#define __INTUIT__

namespace Kernel {
  class Unit;
  class Problem;
};

#include "Kernel/Formula.hpp"

using namespace Kernel;

namespace Shell {

/**
 * Class implementing intuitionistic Semantics
 */
class Intuitionistic
{
public:
  static UnitList intuitionisticSemantics();
  static FormulaUnit* intuitionistic(FormulaUnit* unit);
  static Formula* intuitionistic(Formula*, bool polarity, Term* worldPrefix);
  static char existencePredicateName[7];
  static constexpr char kripkePartialOrderName[15] = "kripkeLessThan";
private:
  static Literal* intuitionistic(Literal*);
  static TermList intuitionistic(TermList, bool polarity, Term* worldPrefix);
  static FormulaList* intuitionistic(FormulaList*, bool polarity, Term* worldPrefix);
}; // class Intuitionistic

}

#endif
