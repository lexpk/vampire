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
 * @file InductionPreprocessor.hpp
 * Defines class InductionPreprocessor
 *
 */

#ifndef __InductionPreprocessor__
#define __InductionPreprocessor__

#include "Forwards.hpp"

namespace Shell
{

class InductionPreprocessor {
public:
  static void preprocess(const Problem& prb);
};

}

#endif /*__InductionPreprocessor__*/