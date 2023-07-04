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
 * @file Intuitionistic.cpp
 * Implements transformations for expressing intuitionistic semantics.
 */

#include "Lib/Environment.hpp"

#include "Kernel/Inference.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Term.hpp"

#include "Shell/Options.hpp"

#include "Intuitionistic.hpp"

using namespace Kernel;
using namespace Shell;


/**
 * Returns the axioms encoding intuitionistic semantics.
 * @warning the problem must be first-order
 */
UnitList Intuitionistic::intuitionisticSemantics()
{
  CALL("Intuitionistic::intuitionistic(Problem* prb)");

  //unsigned existsPredicate = env.signature->addPredicate(existencePredicateName,2);
  unsigned kripkePartialOrder = env.signature->addPredicate(kripkePartialOrderName,2);

  /* UnitList::Iterator uit(prb.units());
  while (uit.hasNext()) {
    Unit* u = uit.next();
    if (u->isClause()) {
      continue;
    }
    FormulaUnit* fu = static_cast<FormulaUnit*>(u);
    FormulaUnit* newFu = intuitionistic(fu);
    if (newFu != fu) {
      uit.replace(newFu);
    } */

    //Add a number of formulas encoding properties of the Kripke structure, in particular
    //that kripkePartialOrder is a partial order, monotonicity of the existencePredicate, and persistency.
    
    //kripkePartialOrder is a partial order.
    Literal* reflexivity = new(2) Literal(kripkePartialOrder,2,false,false);
    reflexivity->nthArgument(0)->makeVar(0);
    reflexivity->nthArgument(1)->makeVar(0);
    Formula* refl = new AtomicFormula(reflexivity);
    FormulaUnit* reflexivityUnit = new FormulaUnit(refl,TheoryAxiom(InferenceRule::INPUT));
    return UnitList(reflexivityUnit);
} // INTUITIONISTIC::intuitionistic(Problem&)
