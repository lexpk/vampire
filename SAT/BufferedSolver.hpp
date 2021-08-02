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
 * @file BufferedSolver.hpp
 * Defines class BufferedSolver.
 *
 * The idea is to buffer clauses that are true, or can be made true, by the ground model
 *
 * @author Giles
 */

#ifndef __BufferedSolver__
#define __BufferedSolver__

#include "Forwards.hpp"

#include "Lib/DArray.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/DHSet.hpp"
#include "Lib/ScopedPtr.hpp"
#include "Lib/Stack.hpp"

#include "SATSolver.hpp"

namespace SAT {

using namespace Lib;

class BufferedSolver : public SATSolver {
public:
  CLASS_NAME(BufferedSolver);
  USE_ALLOCATOR(BufferedSolver);

  BufferedSolver(SATSolver* inner);

  SATClause* getRefutation() final { return _inner->getRefutation(); }
  SATClauseList* getRefutationPremiseList() final {
    return _inner->getRefutationPremiseList();
  }
  void randomizeForNextAssignment(unsigned maxVar) final {
    _inner->randomizeForNextAssignment(maxVar);

    // This is not ideal, but we can't wait till solve, because
    // BufferedSolver would not be forced to consult inner if it already "has an assignment in mind"
    flushUnadded();
    _lastStatus = _inner->solve();
  }

  void addClause(SATClause* cl) final;
  Status solve(unsigned conflictCountLimit) final;
  VarAssignment getAssignment(unsigned var) final;

  bool isZeroImplied(unsigned var) final {
    CALL("BufferedSolver::isZeroImplied");
    ASS_G(var,0); ASS_LE(var,_varCnt);
    // alternatively, we could directly refer to _inner, it must handle variables up to _varCnt as well
    return (var > _varCntInnerOld) ? false : _inner->isZeroImplied(var);
  }
  void collectZeroImplied(SATLiteralStack& acc) final { _inner->collectZeroImplied(acc); }
  SATClause* getZeroImpliedCertificate(unsigned var) final { return _inner->getZeroImpliedCertificate(var); }

  void ensureVarCount(unsigned newVarCnt) final { _inner->ensureVarCount(newVarCnt); _varCnt=max(_varCnt,newVarCnt); }
  unsigned newVar() final { 
    CALL("BufferedSolver::newVar");
    
    ALWAYS(_inner->newVar() == ++_varCnt);
    return _varCnt;
  }
  
  void suggestPolarity(unsigned var,unsigned pol) final { _inner->suggestPolarity(var,pol); }

private:

  // check if @cl is implied by current model, and record it
  // if we choose not to add it at this point
  bool checkAndRecordImplied(SATClause* cl);

  // Add any clauses that have been buffered to _inner and solve.
  void flushUnadded();

  SATSolverSCP _inner;

 /**
  * A buffer for new literals that do not yet appear in the solver
  */
  DHMap<unsigned, bool> _literalBuffer;

  /**
   * Clauses that have not been added to _inner as they are either implied by the assignment of _inner
   * or the variables implicitly set in _literalBuffer
   */
  SATClauseStack _unadded;
  
  /**
   * Index (to _unadded) of the least clause not yet checked wrt the current model.
   */ 
  unsigned _checkedIdx;

  /**
   * Remember the last status returned by solve.
   */
  Status _lastStatus;

  /**
   * Our current varCnt and (of _inner as well).
   */
  unsigned _varCnt;
  
  /**
  * varCnt of _inner at the time of the last flush.
  *
  * Variables larger than this are handled by Buffered
  */
  unsigned _varCntInnerOld;
};

}

#endif // __BufferedSolver__
