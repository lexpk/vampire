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
#include "Kernel/FormulaUnit.hpp"	

using namespace Kernel;

namespace Shell {

/**
 * Class implementing intuitionistic Semantics
 */
class Intuitionistic
{
public:
  static void intuitionistic(Problem& prb);
  static constexpr char kripkePartialOrderName[15] = "kripkeLEQ";
  static constexpr char existencePredicateName[14] = "existsAtWorld";
private:
  static FormulaUnit* intuitionistic(FormulaUnit* fu);
  static Formula* intuitionistic(Formula* f, unsigned varCnt, unsigned kripkePartialOrder, unsigned existsPredicate);
  static Literal* intuitionistic(Literal* l, unsigned varCnt);
  static FormulaUnit* kripkePartialOrderAxiomatization(unsigned kripkePartialOrder);
  static FormulaUnit* existenceAxiomatization(unsigned existsPredicate);
}; // class Intuitionistic

}

#endif
