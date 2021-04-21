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
 * @file TermIndex.cpp
 * Implements class TermIndex.
 */

#include "Lib/DHSet.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"

#include "TermIndexingStructure.hpp"
#include "TermIndex.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Inferences;
using namespace Indexing;

TermIndex::~TermIndex()
{
  delete _is;
}

TermQueryResultIterator TermIndex::getUnifications(TermList t,
	  bool retrieveSubstitutions)
{
  return _is->getUnifications(t, retrieveSubstitutions);
}

TermQueryResultIterator TermIndex::getUnificationsWithConstraints(TermList t,
          bool retrieveSubstitutions)
{
  return _is->getUnificationsWithConstraints(t, retrieveSubstitutions);
}

TermQueryResultIterator TermIndex::getGeneralizations(TermList t,
	  bool retrieveSubstitutions)
{
  return _is->getGeneralizations(t, retrieveSubstitutions);
}

TermQueryResultIterator TermIndex::getInstances(TermList t,
	  bool retrieveSubstitutions)
{
  return _is->getInstances(t, retrieveSubstitutions);
}


void SuperpositionSubtermIndex::handleClause(Clause* c, bool adding)
{
  CALL("SuperpositionSubtermIndex::handleClause");

  if (c->containsFunctionDefinition()) {
    return;
  }

  TimeCounter tc(TC_BACKWARD_SUPERPOSITION_INDEX_MAINTENANCE);

  unsigned selCnt=c->numSelected();
  for (unsigned i=0; i<selCnt; i++) {
    Literal* lit=(*c)[i];
    TermIterator rsti=EqHelper::getRewritableSubtermIterator(lit,_ord);
    while (rsti.hasNext()) {
      if (adding) {
	_is->insert(rsti.next(), lit, c);
      }
      else {
	_is->remove(rsti.next(), lit, c);
      }
    }
  }
}

void SuperpositionLHSIndex::handleClause(Clause* c, bool adding)
{
  CALL("SuperpositionLHSIndex::handleClause");

  TimeCounter tc(TC_FORWARD_SUPERPOSITION_INDEX_MAINTENANCE);

  if (c->containsFunctionDefinition()) {
    return;
  }

  unsigned selCnt=c->numSelected();
  for (unsigned i=0; i<selCnt; i++) {
    Literal* lit=(*c)[i];
    TermIterator lhsi=EqHelper::getSuperpositionLHSIterator(lit, _ord, _opt);
    while (lhsi.hasNext()) {
      TermList lhs=lhsi.next();
      if (adding) {
	_is->insert(lhs, lit, c);
      }
      else {
	_is->remove(lhs, lit, c);
      }
    }
  }
}

void FnDefLHSIndex::handleClause(Clause* c, bool adding)
{
  CALL("FnDefLHSIndex::handleClause");

  TimeCounter tc(TC_FORWARD_SUPERPOSITION_INDEX_MAINTENANCE);

  if (!c->containsFunctionDefinition()) {
    return;
  }

  unsigned cnt = 0;
  for (unsigned i = 0; i < c->length(); i++) {
    Literal* lit=(*c)[i];
    if (!c->isFunctionDefinition(lit)) {
      continue;
    }
    cnt++;
    TermIterator lhsi=EqHelper::getFnDefLHSIterator(lit, c->isReversedFunctionDefinition(lit));
    while (lhsi.hasNext()) {
      TermList lhs=lhsi.next();
      if (adding) {
	_is->insert(lhs, lit, c);
      }
      else {
	_is->remove(lhs, lit, c);
      }
    }
  }
  ASS_EQ(cnt, 1);
}

void IHLHSIndex::handleClause(Clause* c, bool adding)
{
  CALL("IHLHSIndex::handleClause");

  TimeCounter tc(TC_FORWARD_SUPERPOSITION_INDEX_MAINTENANCE);

  for (unsigned i = 0; i < c->length(); i++) {
    Literal* lit=(*c)[i];
    unsigned sig;
    bool hyp = false, rev;
    bool ind = c->isInductionLiteral(lit, sig, hyp, rev);
    if (!ind || !hyp) {
      continue;
    }
    ASS(lit->isEquality());
    TermIterator lhsi=EqHelper::getEqualityArgumentIterator(lit);
    while (lhsi.hasNext()) {
      TermList lhs=lhsi.next();
      if (adding) {
	_is->insert(lhs, lit, c);
      }
      else {
	_is->remove(lhs, lit, c);
      }
    }
  }
}

void ICSubtermIndex::handleClause(Clause* c, bool adding)
{
  CALL("ICSubtermIndex::handleClause");

  TimeCounter tc(TC_FORWARD_SUPERPOSITION_INDEX_MAINTENANCE);

  if (c->containsFunctionDefinition()) {
    return;
  }

  static DHSet<TermList> inserted;

  for (unsigned i = 0; i < c->length(); i++) {
    Literal* lit=(*c)[i];
    unsigned sig;
    bool hyp = true, rev;
    bool ind = c->isInductionLiteral(lit, sig, hyp, rev);
    if (!ind || hyp) {
      continue;
    }
    ASS(lit->isEquality());
    NonVariableIterator nvi(lit);
    while (nvi.hasNext()) {
      TermList t=nvi.next();
      if (!inserted.insert(t)) {
        //It is enough to insert a term only once per clause.
        //Also, once we know term was inserted, we know that all its
        //subterms were inserted as well, so we can skip them.
        nvi.right();
        continue;
      }
      if (adding) {
	_is->insert(t, lit, c);
      }
      else {
	_is->remove(t, lit, c);
      }
    }
  }
}

void DemodulationSubtermIndex::handleClause(Clause* c, bool adding)
{
  CALL("DemodulationSubtermIndex::handleClause");

  TimeCounter tc(TC_BACKWARD_DEMODULATION_INDEX_MAINTENANCE);

  if (c->containsFunctionDefinition()) {
    return;
  }

  static DHSet<TermList> inserted;

  unsigned cLen=c->length();
  for (unsigned i=0; i<cLen; i++) {
    // it is true (as stated below) that inserting only once per clause would be sufficient
    // however, vampire does not guarantee the order of literals stays the same in a clause (selected literals are moved to front)
    // so if the order changes while a clause is in the index (which can happen with "-sa otter")
    // the removes could be called on different literals than the inserts!
    inserted.reset();
    Literal* lit=(*c)[i];
    NonVariableIterator nvi(lit);
    while (nvi.hasNext()) {
      TermList t=nvi.next();
      if (!inserted.insert(t)) {
	//It is enough to insert a term only once per clause.
	//Also, once we know term was inserted, we know that all its
	//subterms were inserted as well, so we can skip them.
	nvi.right();
	continue;
      }
      if (adding) {
	_is->insert(t, lit, c);
      }
      else {
	_is->remove(t, lit, c);
      }
    }
  }
}


void DemodulationLHSIndex::handleClause(Clause* c, bool adding)
{
  CALL("DemodulationLHSIndex::handleClause");

  if (c->length()!=1) {
    return;
  }

  TimeCounter tc(TC_FORWARD_DEMODULATION_INDEX_MAINTENANCE);

  Literal* lit=(*c)[0];
  TermIterator lhsi=EqHelper::getDemodulationLHSIterator(lit, true, _ord, _opt, c->containsFunctionDefinition(), c->isReversedFunctionDefinition(lit));
  while (lhsi.hasNext()) {
    if (adding) {
      _is->insert(lhsi.next(), lit, c);
    }
    else {
      _is->remove(lhsi.next(), lit, c);
    }
  }
}
