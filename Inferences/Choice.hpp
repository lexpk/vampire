
/*
 * File BoolSimp.hpp.
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
 * @file BoolSimp.hpp
 * Defines class BoolSimp.
 */

#ifndef __CHOICE__
#define __CHOICE__

#include "Forwards.hpp"

#include "InferenceEngine.hpp"

namespace Inferences {

class Choice : public GeneratingInferenceEngine
{
  public:
    CLASS_NAME(Choice);
    USE_ALLOCATOR(Choice);

    ClauseIterator generateClauses(Clause* premise);

  private:
    struct SubtermsFn;
    struct IsChoiceTerm;
    struct ResultFn;
    struct AxiomsIterator;
    static Clause* createChoiceAxiom(TermList op, TermList set);
};

}

#endif
