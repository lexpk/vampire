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
 * @file InferenceStore.hpp
 * Defines class InferenceStore.
 */


#ifndef __InferenceStore__
#define __InferenceStore__

#include <utility>
#include <ostream>

#include "Forwards.hpp"

#include "Lib/Allocator.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/DHMultiset.hpp"
#include "Lib/Stack.hpp"
#include "Lib/VString.hpp"

#include "Kernel/Signature.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"

namespace Kernel {

using namespace Lib;

class InferenceStore
{
public:
  CLASS_NAME(InferenceStore);
  USE_ALLOCATOR(InferenceStore);
  
  static InferenceStore* instance();

  typedef List<int> IntList;

  struct FullInference
  {
    FullInference(unsigned premCnt) : csId(0), premCnt(premCnt) { }

    void* operator new(size_t,unsigned premCnt)
    {
      size_t size=sizeof(FullInference)+premCnt*sizeof(Unit*);
      size-=sizeof(Unit*);

      return ALLOC_KNOWN(size,"InferenceStore::FullInference");
    }

    size_t occupiedBytes()
    {
      size_t size=sizeof(FullInference)+premCnt*sizeof(Unit*);
      size-=sizeof(Unit*);
      return size;
    }

    void increasePremiseRefCounters();

    int csId;
    unsigned premCnt;
    InferenceRule rule;
    Unit* premises[1];
  };

  void recordSplittingNameLiteral(Unit* us, Literal* lit);
  void recordIntroducedSymbol(Unit* u, SymbolType st, unsigned number);  
  void recordIntroducedSplitName(Unit* u, vstring name);

  void outputUnsatCore(ostream& out, Unit* refutation);
  void outputProof(ostream& out, Unit* refutation);
  void outputProof(ostream& out, UnitList* units);

  UnitIterator getParents(Unit* us, InferenceRule& rule);
  UnitIterator getParents(Unit* us);

  vstring getUnitIdStr(Unit* cs);

  struct ProofPrinter
  {
    CLASS_NAME(ProofPrinter);
    USE_ALLOCATOR(ProofPrinter);

    ProofPrinter(ostream& out, InferenceStore* is)
    : _is(is), out(out)
    {
      CALL("InferenceStore::ProofPrinter::ProofPrinter");

      outputAxiomNames=env.options->outputAxiomNames();
      delayPrinting=true;
    }

    void scheduleForPrinting(Unit* us)
    {
      CALL("InferenceStore::ProofPrinter::scheduleForPrinting");

      outKernel.push(us);
      handledKernel.insert(us);
    }

    virtual ~ProofPrinter() {}

    virtual void print()
    {
      CALL("InferenceStore::ProofPrinter::print");

      while(outKernel.isNonEmpty()) {
        Unit* cs=outKernel.pop();
        handleStep(cs);
      }
      if(delayPrinting) printDelayed();
    }

  protected:

    virtual bool hideProofStep(InferenceRule rule)
    {
      return false;
    }

    void requestProofStep(Unit* prem)
    {
      if (!handledKernel.contains(prem)) {
        handledKernel.insert(prem);
        outKernel.push(prem);
      }
    }

    virtual void printStep(Unit* cs);
    void handleStep(Unit* cs);
    void printDelayed();

    Stack<Unit*> outKernel;
    Set<Unit*> handledKernel; // use UnitSpec to provide its own hash and equals
    Stack<Unit*> delayed;

    InferenceStore* _is;
    ostream& out;

    bool outputAxiomNames;
    bool delayPrinting;
  };

private:
  InferenceStore();

  struct TPTPProofPrinter;
  struct ProofCheckPrinter;
  struct ProofPropertyPrinter;

  ProofPrinter* createProofPrinter(ostream& out);

  DHMultiset<Clause*> _nextClIds;

  DHMap<Unit*, Literal*> _splittingNameLiterals;


  /** first records the type of the symbol (PRED,FUNC or TYPE_CON), second is symbol number */
  typedef pair<SymbolType,unsigned> SymbolId;  
  typedef Stack<SymbolId> SymbolStack;
  DHMap<unsigned,SymbolStack> _introducedSymbols;
  DHMap<unsigned,vstring> _introducedSplitNames;

};

};

#endif /* __InferenceStore__ */
