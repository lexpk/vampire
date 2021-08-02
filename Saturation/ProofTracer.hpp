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
 * @file Saturation/ProofTracer.hpp
 * Defines class ProofTracer.
 */

#ifndef __Saturation_ProofTracer__
#define __Saturation_ProofTracer__

#include "Forwards.hpp"

#include "Parse/TPTP.hpp"
#include "Indexing/ClauseVariantIndex.hpp"
#include "Kernel/RCClauseStack.hpp"

namespace Saturation {

struct ProofTracer {
  CLASS_NAME(ProofTracer);
  USE_ALLOCATOR(ProofTracer);

  /**
   * Initialize the ProofTracer by reading some proofs from the given file (traceFileNames).
   * (Tracing of more than one proof is envisaged for the future
   * but currently only one proof file is supported.)
   *
   * Note: To produce a loadable proof run vampire with "-p tptp" (and consider adding "--output_axiom_names on")
   */
  void init(const vstring& traceFileNames);

  /**
   * Various events by which SaturationAlgorithm notifies the tracer about clause happenings.
   *
   * On onNewClause uses variant index to match up a clause from the traced proof with the newly derived.
   * Other events may only respond to already matched up clauses (ASS(cl->isTraced())).
   *
   * The main idea behind events is to be able to identify and report as soon as possible
   * that a particular expected inference will not happen in the new saturation (the way it happened in the old one).
   *
   * For instance, if we haven't seen all the expected input clauses by the time onInputFinished is called,
   * there is no chance to flawlessly trace the original proof anymore (as some of the required initial clauses is now known to be missing).
   */

  void onNewClause(Clause* cl);
  void onInputClause(Clause* cl);
  void onInputFinished();
  void onActivation(Clause* cl);
  void onActivationFinished(Clause* cl);

  void finalInfo()
  {
    CALL("ProofTracer::finalInfo");
    _tp->finalInfo();
  }

  // helper functions and subclasses

  static void printWithStore(Clause* cl) {
    switch(cl->store()) {
      case Clause::Store::PASSIVE:
        cout << "PASSIVE: ";
        break;
      case Clause::Store::ACTIVE:
        cout << "ACTIVE: ";
        break;
      case Clause::Store::UNPROCESSED:
        cout << "UNPROCESSED:";
        break;
      case Clause::Store::NONE:
        cout << "NONE: ";
        break;
      case Clause::Store::SELECTED:
        cout << "SELECTED: ";
        break;
    }
    cout << cl->toString() << endl;
  }

  enum InferenceKind {
    ICP = 0, // INPUT / PREPROCESSING / CLAUSIFICATION anything larger than this should end up in the TracedProof
    TRIVSIMP = 1,
    SIMPLIFYING = 2,  // TODO: let's see whether we don't also need to distinguish FWD and BWD!
    GENERATING = 3,
  };

  /* a temporary struct we get from parsing the TPTP proof file; becomes obsolete once we get a TracedProof object out of it */
  struct ParsedProof {
    CLASS_NAME(ParsedProof);
    USE_ALLOCATOR(ParsedProof);

    UnitList* units;
    DHMap<unsigned, vstring> names;
    DHMap<Unit*,Parse::TPTP::SourceRecord*> sources;
  };

  // maybe could use Store for this, but let's keep some flexibility
  // this is what we know about the actual runs clause corresponding to this one at the moment
  /*
  enum ClauseState {
    NONE = 0,        // the starting state; somehow before it's even born
    NEW = 1,         // every new clause is subject to IS before it's moved to Unprocessed
    UNPRO = 2,       // every unprocessed clause is subject to FowardSimplification before it's moved to Passive
                     // will also do BackwardSimplification just after in Otter
    PASSIVE = 3,     // when a passive clause gets selected, it is again subject to FowardSimplification (in Discount),
                     // then it does BW while getting activated after which it triggers Generating Inferences
                     // a passive clause can be removed by a Backward Simplification in Otter (and LRS)
    ACTIVE = 4,      // Active clauses generate new clauses and can be removed via Backward Simplifications
    GONE = 5
  };
  */

  struct TracedClauseInfo {
    CLASS_NAME(TracedClauseInfo);
    USE_ALLOCATOR(TracedClauseInfo);

    vstring _name;     // the Unit::number of the clause in the original derivation
    vstring _inf;      // the name of the inference as read from the original derivation file
    InferenceKind _ik; // the kind of inference this clause arose by

    TracedClauseInfo(const vstring& name, const vstring& inf, InferenceKind ik) : _name(name), _inf(inf), _ik(ik), _numAwokenParents(0) {}

    Stack<Clause*> _parents;  // premises
    Stack<Clause*> _children; // the opposite arrows

    bool isInital() {
      return _parents.size() == 0;
    }

    // should be only the final empty clause
    bool isTerminal() {
      return _children.size() == 0;
    }

    // the clause(s) from the new run we think should play the same role in the new proof
    RCClauseStack _stalkees;

    int _numAwokenParents;
  };

  struct TracedProof {
    CLASS_NAME(TracedProof);
    USE_ALLOCATOR(TracedProof);

    void init();
    void onInputFinished();

    void finalInfo();

    void regNewClause(Clause* cl, const vstring& name, const vstring& inf, InferenceKind ik) {
      CALL("ProofTracer::TracedProof::regNewClause");

      ALWAYS(_clInfo.insert(cl,new TracedClauseInfo(name,inf,ik)));

      _variantLookup->insert(cl);

      ClauseList::push(cl,_inOrder);
    }

    void regChildParentPair(Clause* ch, Clause* p) {
      CALL("ProofTracer::TracedProof::regChildParentPair");

      _clInfo.get(ch)->_parents.push(p);
      _clInfo.get(p)->_children.push(ch);
    }

    void setEmpty(Clause* cl) {
      CALL("ProofTracer::TracedProof::setEmpty");
      ASS_EQ(_theEmpty,0); // only set once
      _theEmpty = cl;
    }

    Clause* findVariant(Clause* cl) {
      CALL("ProofTracer::TracedProof::findVariant");

      Clause* res = 0;

      ClauseIterator it = _variantLookup->retrieveVariants(cl);
      if (it.hasNext()) {
        res = it.next();
        ASS(!it.hasNext());
      }
      return res;
    }

    TracedClauseInfo* getClauseInfo(Clause* cl) {
      CALL("ProofTracer::TracedProof::getClauseInfo");
      return _clInfo.get(cl);
    }

    void initalBorn() {
      CALL("ProofTracer::TracedProof::initalBorn");
      _unbornInitials--;
    }

    void listExpecteds();
    void listExpectedsDetails();

    TracedProof() : _inOrder(nullptr), _theEmpty(0), _variantLookup(new Indexing::HashingClauseVariantIndex()), _unbornInitials(0), _lastActivationMatch(0) {}
    ~TracedProof() { delete _variantLookup; }

  // private:
    ClauseList* _inOrder;

    Clause* _theEmpty;
    DHMap<Clause*, TracedClauseInfo*> _clInfo;

    Indexing::ClauseVariantIndex* _variantLookup;

    int _unbornInitials;

    Clause* _lastActivationMatch;

    /* Set of clause that are expected to appear as their parents (in the traced proof)
     *  have already been spotted.
     *  (Could start with all the initial clauses in expecting, but those are already taken care of by the _unbornInitials counter.)
     **/
    DHSet<Clause*> _expecting;
  };

  ParsedProof* getParsedProof(const vstring& traceFileNames);
  TracedProof* prepareTracedProof(ParsedProof* pp);
  void initializeTracedProof(TracedProof* tp);

  ProofTracer() : _tp(0) {}

private:
  TracedProof* _tp;

  Clause* unitToClause(Unit* u);
};

}

#endif // __Saturation_ProofTracer__
