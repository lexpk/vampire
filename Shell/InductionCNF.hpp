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
 * @file InductionCNF.hpp
 * Defines class InductionCNF implementing the new CNF transformation.
 * @since 19/11/2015 Manchester
 */

#ifndef __InductionCNF__
#define __InductionCNF__

#include "Lib/Stack.hpp"
#include "Lib/List.hpp"
#include "Lib/DArray.hpp"
#include "Lib/Deque.hpp"
#include "Lib/STLAllocator.hpp"
#include "Lib/SmartPtr.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/SharedSet.hpp"
#include "Kernel/Substitution.hpp"
#include "Kernel/Formula.hpp" //TODO AYB remove, it is not required in master

namespace Kernel {
  class Formula;
  class FormulaUnit;
  class Clause;
  class Unit;
  class Literal;
};

#include <list>

namespace Shell {

class InductionCNF
{
public:
  InductionCNF()
    : _collectedVarSorts(false) {}

  void clausify(FormulaUnit* unit, Stack<Clause*>& output);
  const Substitution& subst() { return _globalSubst; }
private:

  FormulaUnit* _beingClausified;

  /**
   * Queue of formulas to process.
   *
   * Although queue sounds reasonable, the algorithm works with any order of the elements here.
   * Prioritizing should respect sub-formula relation,
   * and the algorithm will work better if subformulas are recognized.
   * However, not merging distinct occurrences of a single subformula
   * from the input does not compromise correctness.
   */
  Deque<Formula*> _queue;

  Substitution _globalSubst; // used for skolem bindings of the form <existential variable z, corresponding Skolem term f_z(U,V,...) >

  #define SIGN bool
  #define POSITIVE true
  #define NEGATIVE false

  // generalized clause
  struct GenClause {
    CLASS_NAME(InductionCNF::GenClause);
    USE_ALLOCATOR(InductionCNF::GenClause);

    GenClause(unsigned size)
      : valid(true), _literals(size), _size(0) {}

    bool valid; // used for lazy deletion from Occurrences(s); see below

    DArray<Formula*> _literals; // TODO: remove the extra indirection and allocate inside GenClause
    unsigned _size;

    DArray<Formula*>::Iterator genLiterals() {
      ASS_EQ(_size, _literals.size());
      return DArray<Formula*>::Iterator(_literals);
    }

    // Position of a gen literal in _genClauses
    list<SmartPtr<GenClause>,STLAllocator<SmartPtr<GenClause>>>::iterator iter;
  };

  typedef SmartPtr<GenClause> SPGenClause;

  Clause* toClause(SPGenClause gc);

  typedef list<SPGenClause,STLAllocator<SPGenClause>> GenClauses;

  /**
   * pushLiteral is responsible for tautology elimination. Whenever it sees two
   * generalised literals with the opposite signs, the entire generalised clause
   * is discarded. Whenever it sees more than one occurrence of a generalised
   * literal, only one copy is kept.
   *
   * pushLiteral two kinds of tautologies: between shared literals and between
   * copies of formulas. The former is possible because syntactically
   * equivalent literals are shared and therefore can be compared by pointer.
   * The latter can occur after inlining of let-s and ite-s. Removing tautologies
   * between formulas is important for traversal of the list of occurrences,
   * without it popping the first occurrence of a formula will invalidate the
   * entire generalised clause, and other occurrences will never be seen.
   */
  DHSet<Literal*> _literalsCache;
  inline void pushLiteral(SPGenClause gc, Formula* f) {
    CALL("InductionCNF::pushLiteral");
    auto conn = f->connective();
    ASS_NEQ(conn, NOT);

    if (conn == LITERAL) {
      Literal* l = f->literal();
      ASS(l->shared());
      if (_literalsCache.find(Literal::complementaryLiteral(l))) {
        gc->valid = false;
      }
      if (!_literalsCache.insert(l)) {
        return;
      }
    }

    gc->_literals[gc->_size++] = f;
  }

  /**
   * Collection of the current set of generalized clauses.
   * (It is a doubly-linked list for constant time deletion.)
   */
  GenClauses _genClauses;
  DHMap<Formula*,SIGN> _signs;

  using Occurrence = pair<SPGenClause,unsigned>;

  /**
   * Occurrences represents a list of occurrences in valid generalised clauses.
   * Occurrences is used instead of an obvious List<Occurrence> because it
   * maintains a (1) convenient (2) constant time size() method.
   *
   * (1) Occurrences maintains a List<Occurrence> * _occurrences, where each
   *     Occurrence points to a generalised clause which can become invalid.
   *     We are only interested in occurrences in valid generalised clauses.
   *     It wouldn't be enough to call _occurrences->length(), as it might
   *     count occurrences in invalid generalised clauses.
   *
   * (2) List::length is O(n) in the version of stdlib we are using. Instead of
   *     calling it we maintain the size in a variables (_size) that is updated
   *     in two situations:
   *     - whenever the list of occurrences changes (by calling Occurrences's
   *       own add(), append() and pop() methods)
   *     - whenever a generalised clause is invalidated. In that case InductionCNF
   *       calls Occurrences::decrement() of every list of occurrences that has
   *       an occurrence in this newly invalid generalised clause
   */
  class Occurrences {
  private:
    List<Occurrence>* _occurrences;
    unsigned _size;

  public:
    CLASS_NAME(InductionCNF::Occurrences);
    USE_ALLOCATOR(InductionCNF::Occurrences);

    Occurrences() : _occurrences(nullptr), _size(0) {}

    inline void add(SPGenClause gc, unsigned position) {
      Occurrence occ = make_pair(gc, position);
      List<Occurrence>::push(occ, _occurrences);
      _size++;
    }

    inline void append(Occurrences occs) {
      _occurrences = List<Occurrence>::concat(_occurrences, occs._occurrences);
      _size += occs._size;
    }

    bool isNonEmpty() {
      while (true) {
        if (List<Occurrence>::isEmpty(_occurrences)) {
          ASS_EQ(_size, 0);
          return false;
        }
        if (!_occurrences->head().first->valid) {
          List<Occurrence>::pop(_occurrences);
        } else {
          ASS_G(_size, 0);
          return true;
        }
      }
    }

    void decrement() {
      ASS_G(_size, 0);
      _size--;
    }

    Occurrence pop() {
      ASS(isNonEmpty());
      Occurrence occ = List<Occurrence>::pop(_occurrences);
      ASS(occ.first->valid);
      decrement();
      return occ;
    }

    void replaceBy(Formula* f) {
      CALL("Occurrences::replaceBy");
      Occurrences::Iterator occit(*this);
      while (occit.hasNext()) {
        Occurrence occ = occit.next();
        occ.first->_literals[occ.second] = f;
      }
    }

    class Iterator {
    public:
      Iterator(Occurrences &occurrences): _iterator(List<Occurrence>::DelIterator(occurrences._occurrences)) {}

      inline bool hasNext() {
        while (_iterator.hasNext()) {
          Occurrence occ = _iterator.next();
          if (!occ.first->valid) {
            _iterator.del();
            continue;
          }
          _current = occ;
          return true;
        }
        return false;
      }
      Occurrence next() {
        return _current;
      }
    private:
      List<Occurrence>::DelIterator _iterator;
      Occurrence _current;
    };
  };

  void addToGenClauses(SPGenClause gc) {
    if (gc->valid) {
      _genClauses.push_front(gc);
      gc->iter = _genClauses.begin();

      auto igl = gc->genLiterals();
      unsigned position = 0;
      while (igl.hasNext()) {
        Formula* f = igl.next();
        Occurrences* occurrences = _occurrences.findPtr(f);
        if (occurrences) {
          occurrences->add(gc, position);
        }
        position++;
      }
    }
  }

  void introduceGenClause(Formula* f) {
    SPGenClause gc = SPGenClause(new GenClause(1));
    gc->_literals[gc->_size++] = f;
    addToGenClauses(gc);
  }

  void introduceExtendedGenClause(Occurrence occ, const vvector<Formula*>& fs) {
    CALL("InductionCNF::introduceExtendedGenClause(Occurrence, const vvector<Formula*>&)");

    SPGenClause gc = occ.first;
    unsigned position = occ.second;

    unsigned size = gc->_size + fs.size() - 1;
    SPGenClause newGc = SPGenClause(new GenClause(size));

    ASS(_literalsCache.isEmpty());

    auto gcit = gc->genLiterals();
    unsigned i = 0;
    while (gcit.hasNext()) {
      Formula* f = gcit.next();
      if (i == position) {
        for (const auto& f : fs) {
          pushLiteral(newGc, f);
        }
      } else {
        pushLiteral(newGc, f);
      }
      i++;
    }

    _literalsCache.reset();

    addToGenClauses(newGc);
  }

  Occurrence pop(Occurrences &occurrences) {
    CALL("InductionCNF::pop");

    Occurrence occ = occurrences.pop();
    occ.first->valid = false;
    _genClauses.erase(occ.first->iter);

    auto glit = occ.first->genLiterals();
    while (glit.hasNext()) {
      Formula* f = glit.next();

      if (f->connective() == LITERAL) {
        ASS(f->literal()->shared());
        continue;
      }

      Occurrences* fOccurrences = _occurrences.findPtr(f);
      if (fOccurrences) {
        fOccurrences->decrement();
      }
    }

    return occ;
  }

  DHMap<Formula*, Occurrences> _occurrences;

  /** map var --> sort */
  DHMap<unsigned,TermList> _varSorts;
  bool _collectedVarSorts;

  Term* createSkolemTerm(unsigned var, VarSet* free);

  // caching of free variables for subformulas
  DHMap<Formula*,VarSet*> _freeVars;
  VarSet* freeVars(Formula* g);

  void skolemise(QuantifiedFormula* g);

  void enqueue(Formula* formula, SIGN s, Occurrences occurrences = Occurrences()) {
    CALL("InductionCNF::enqueue");
    ALWAYS(s == _signs.findOrInsert(formula, s));
    if (formula->connective() == LITERAL) {
      ASS(formula->literal()->shared());
      return;
    }

    ASS_NEQ(formula->connective(), NOT);

    if (_occurrences.find(formula)) {
      Occurrences oldOccurrences;
      _occurrences.pop(formula, oldOccurrences);
      occurrences.append(oldOccurrences);
    } else {
      _queue.push_back(formula);
    }
    ALWAYS(_occurrences.insert(formula, occurrences));
  }

  void process(Formula* g);
  void process(JunctionFormula* g, Occurrences &occurrences, SIGN s);
  void process(BinaryFormula* g, Occurrences &occurrences, SIGN s);
  void process(QuantifiedFormula* g, Occurrences &occurrences, SIGN s);
}; // class InductionCNF

}
#endif
