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
 * @file RobSubstitution.hpp
 * Defines class RobSubstitution.
 *
 */

#if VHOL

#include "Kernel/HOLUnification.hpp"
#include "Kernel/ApplicativeHelper.hpp"

#include "Lib/SkipList.hpp"

namespace Kernel
{

namespace UnificationAlgorithms {

#define DEBUG_ITERATOR(LVL, ...) if (LVL <= 0) DBG(__VA_ARGS__)
class HOLUnification::HigherOrderUnifiersIt: public IteratorCore<RobSubstitutionTL*> {
public:

  using AH = ApplicativeHelper;

  HigherOrderUnifiersIt(TermList t1, TermList t2, RobSubstitutionTL* subst, bool funcExt) :
    _used(false), _topLevel(true), _funcExt(funcExt), _depth(0), 
    _freshVar(0, VarBank::FRESH_BANK), _subst(subst){
    CALL("HOLUnification::HigherOrderUnifiersIt::HigherOrderUnifiersIt");

    if(!trySolveTrivialPair(t1,t2)){
      _unifPairs.insert(HOLConstraint(t1,t2));
    }

    DEBUG_ITERATOR(1, "starting iterator with\n ", *this)

    BacktrackData bd;
    _bdStack->push(bd);
    _bindings->push(TermStack());
  }
  
  ~HigherOrderUnifiersIt() {
    CALL("HOLUnification::HigherOrderUnifiersIt::~HigherOrderUnifiersIt");
  }

  friend std::ostream& operator<<(std::ostream& out, HigherOrderUnifiersIt const& self)
  { return out << "Backtrack depth " << self._bdStack->size() << "\nBindings " << 
            *self._bindings << "\nCurr subst " << *self._subst << "\nUnif pairs " << self._unifPairs; }

  bool solved() {
    CALL("HOLUnification::HigherOrderUnifiersIt::solved");

    SkipList<HOLConstraint,HOLCnstComp>::RefIterator it(_unifPairs);
    return !it.hasNext() || it.next().flexFlex();
  }

  bool trySolveTrivialPair(TermList t1, TermList t2){
    CALL("HOLUnification::HigherOrderUnifiersIt::trySolveTrivialPair");

    if(t1.isVar() && t2.isVar()){
      if(t1 == t2) return true;
      _subst->bind(t1, t2);
      return true;
    }
    return false;
  }

  bool backtrack() {
    CALL("HOLUnification::HigherOrderUnifiersIt::backtrack");

    bool success = false;
    while(!_bdStack->isEmpty() && !success){
      _depth--;
      _bdStack->pop().backtrack();
      // if there are alterntative bindings available stop bracktracking
      success = !_bindings->top().isEmpty();
    }
    return success;
  }

  void applyBindingToPairs(){
    CALL("HOLUnification::HigherOrderUnifiersIt::applyBindingToPairs");

    Stack<HOLConstraint> temp;
    while(!_unifPairs.isEmpty()){
      HOLConstraint pair = popFromUnifPairs(_bdStack->top());
      TermList lhs = pair.lhs();
      TermList rhs = pair.rhs();
      temp.push(HOLConstraint(lhs.whnfDeref(_subst), rhs.whnfDeref(_subst)));
    }

    while(!temp.isEmpty()){
      addToUnifPairs(temp.pop(), _bdStack->top());
    }
  }

  bool hasNext() {
    CALL("HOLUnification::HigherOrderUnifiersIt::hasNext");
    
    static unsigned depth = env.options->higherOrderUnifDepth();

    if(solved() && !_used)
    { return true; }

    _used = false;
 
    DEBUG_ITERATOR(1, "has next called with\n ", *this)

    // the logic here is really convoluted and should be cleaned up
    // the main complexity is due to the depth limit
    // Once the limit is reached, we continue popping constraints until 
    // we reach a flexRigid pair and then stop and return
    // The next time we call hasNext, the system will be in a solved state
    // if next() has been called in between, since next clears all unif 
    // pairs. Hence a backtrack will take place

    bool forward = !solved() || backtrack();
    while(forward && !solved()){
      if(_unifPairs.top().flexRigid() && _depth == depth)
      { break; }
 
      auto con = popFromUnifPairs(_bdStack->top());

      DEBUG_ITERATOR(2, "Next pair\n ", con)

      TermList lhs = con.lhs();
      TermList rhs = con.rhs();
      TermList lhsHead = con.lhsHead();
      TermList rhsHead = con.rhsHead();
 
      ASS(!lhsHead.isVar() || !rhsHead.isVar()); // otherwise we would be solved
      ASS(lhs.isVar() || rhs.isVar() || SortHelper::getResultSort(lhs.term()) == SortHelper::getResultSort(rhs.term()));

      AH::normaliseLambdaPrefixes(lhs,rhs);    

      if(lhs == rhs){ continue; }

      if(con.rigidRigid()){
        TermList s = con.sort();
        if(_funcExt && _depth == 0 && (s.isArrowSort() || s.isVar() || (s.isBoolSort() && !_topLevel))){
          addToUnifPairs(con, _bdStack->top());
          break;
        }
      }

      if(lhsHead == rhsHead){
        ASS(con.rigidRigid());
        // TODO deal with sorts?

        TermStack lhsArgs;
        TermStack rhsArgs;
        TermStack sorts;
        AH::getLambdaPrefSorts(lhs,sorts);
        AH::getHeadAndArgs(lhs, lhsHead, lhsArgs);
        AH::getHeadAndArgs(rhs, rhsHead, rhsArgs);
        ASS(lhsArgs.size() == rhsArgs.size()); // size must be same due to normalisation of prefixes above

        for(unsigned i = 0; i < lhsArgs.size(); i++){
          auto t1 = lhsArgs[i].whnfDeref(_subst);
          if(!t1.isVar()) t1 = AH::surroundWithLambdas(t1, sorts, /* traverse stack from top */ true);
          auto t2 = rhsArgs[i].whnfDeref(_subst);   
          if(!t2.isVar()) t2 = AH::surroundWithLambdas(t2, sorts, true);                 
          
          if(!trySolveTrivialPair(t1,t2)){
            addToUnifPairs(HOLConstraint(t1,t2), _bdStack->top());
          }
        }

      } else if(con.flexRigid()){
        TermList flexTerm  = lhsHead.isVar() ? lhs : rhs;
        TermList rigidTerm = lhsHead.isVar() ? rhs : lhs;        
        TermList flexHead  = lhsHead.isVar() ? lhsHead : rhsHead;

        if(_bdStack->size() == _bindings->size()){
          // reached here not via a backtrack. Need to add new bindings to bindings

          // oracle calls. no point calling oracles if we reach here via a backtrack
          // they must have already failed
          BacktrackData tempBD;
          _subst->bdRecord(tempBD);
          auto res = HOLUnification::fixpointUnify(flexTerm, rigidTerm, _subst);
          _subst->bdDone();

          if(res == OracleResult::OUT_OF_FRAGMENT){
            tempBD.backtrack();
            // TODO pattern oracle
            // TODO solid oracle?
          } else if (res == OracleResult::SUCCESS){
            tempBD.commitTo(_bdStack->top());
            tempBD.drop();
            applyBindingToPairs();
            continue; // TODO apply new binding to pairs...???
          } else {
            forward = backtrack();
            continue;
          }

          TermStack projAndImitBindings;
          BacktrackData& bd = _bdStack->top();
          bd.addClosure([this, fv = _freshVar](){ _freshVar = fv; });

          AH::getProjAndImitBindings(flexTerm, rigidTerm, projAndImitBindings, _freshVar);
      
          if(projAndImitBindings.isEmpty()){
            // no bindings for this pair of terms
            forward = backtrack();
            continue;
          }

          backtrackablePush(*_bindings,projAndImitBindings,bd);
        }
        
        _depth++;
        addToUnifPairs(con, _bdStack->top()); // add back to pairs with old data
        BacktrackData bd;
        _bdStack->push(bd); // reached a branch point 
        
        ASS(_bindings->top().size());
        TermList binding = _bindings->top().pop(); 
       
        _subst->bdRecord(_bdStack->top());        
        _subst->bind(flexHead, binding);
        _subst->bdDone();

        applyBindingToPairs();

      } else {
        // clash
        forward = backtrack();
      }

      _topLevel = false;
    }

    return forward;
  }

  RobSubstitutionTL* next() {
    CALL("HOLUnification::HigherOrderUnifiersIt::next");

    // turn remaining unification pairs into standard constraints
    // these can either be the flex-flex pairs, or if depth limit reached
    // these can include other pairs as well
    BacktrackData& bd = _bdStack->top();
    _subst->bdRecord(bd);    
    while(!_unifPairs.isEmpty()){
      HOLConstraint con = popFromUnifPairs(bd);
      UnifConstraint c(con.lhs(), con.rhs());
      _subst->pushConstraint(c);      
    }
    _subst->bdDone();
    _used = true;
    return _subst;
  }
  
  HOLConstraint popFromUnifPairs(BacktrackData& bd){
    CALL("HigherOrderUnifiersIt::popFromUnifPairs");

    auto con = _unifPairs.pop();
    bd.addClosure([this, c = con](){ _unifPairs.insert(c); });
    return con;
  }

  void addToUnifPairs(HOLConstraint con, BacktrackData& bd){
    CALL("HigherOrderUnifiersIt::addToUnifPairs");

    _unifPairs.insert(con);
    bd.addClosure([this, c = con ](){ _unifPairs.remove(c); });
  }

private:

  class HOLCnstComp
  {
  public:
    inline
    static Comparison compare(const HOLConstraint& hc1, const HOLConstraint& hc2)
    {
      CALL("HOLUnification::HOLCnstComp::compare");

      auto compareTerms = [](TermList t1, TermList t2){
        if(t1.isVar()){
          if(t2.isVar()){
            return (t1.var() < t2.var()) ? LESS : (t1.var() > t2.var())? GREATER : EQUAL;
          }
          return LESS;
        } else if(t2.isVar()){
          return GREATER;
        }
        
        unsigned id1 = t1.term()->getId();
        unsigned id2 = t2.term()->getId();        

        return (id1<id2)? LESS : (id1>id2)? GREATER : EQUAL;
      };

      if(hc1.rigidRigid() && !hc2.rigidRigid()){
        return LESS;
      } else if (hc2.rigidRigid() && !hc1.rigidRigid()){
        return GREATER;
      } else if (hc1.flexRigid() && hc2.flexFlex()){
        return LESS;
      } else if (hc2.flexRigid() && hc1.flexFlex()){
        return GREATER;
      } 
     
      auto res = compareTerms(hc1.lhs(), hc2.lhs());
      if(res == EQUAL){
        res = compareTerms(hc1.rhs(), hc2.rhs());
      }
      return res;
    }
  };

  bool _used;
  bool _topLevel;
  bool _funcExt;
  unsigned _depth;
  SkipList<HOLConstraint,HOLCnstComp> _unifPairs;
  Recycled<Stack<BacktrackData>> _bdStack;
  Recycled<Stack<TermStack>> _bindings;
  TermList _freshVar;
  RobSubstitutionTL* _subst;
};

SubstIterator HOLUnification::unifiers(TermList t1, TermList t2, RobSubstitutionTL* sub, bool topLevelCheck)
{
  CALL("HOLUnification::unifiers");


  if(sub->sameTermContent(t1,t2)) return pvi(getSingletonIterator(sub));

  if(topLevelCheck){
    // if topLevelCheck is set, we want to check that we
    // don't return a constraint of the form t1 != t2
    if(t1.isVar() || t2.isVar()){
      auto var = t1.isVar() ? t1 : t2;
      auto otherTerm = var == t1 ? t2 : t1;
      auto res = fixpointUnify(var,otherTerm,sub);
      if(res == OracleResult::SUCCESS) return pvi(getSingletonIterator(sub));
      if(res == OracleResult::FAILURE) return SubstIterator::getEmpty();
      if(res == OracleResult::OUT_OF_FRAGMENT) return SubstIterator::getEmpty();
    } else {
      if(!ApplicativeHelper::splittable(t1, true) || !ApplicativeHelper::splittable(t2, true)){
        return SubstIterator::getEmpty();
      }
    }
  }

  return vi(new HigherOrderUnifiersIt(t1, t2, sub, _funcExt));    
}

SubstIterator HOLUnification::postprocess(RobSubstitutionTL* sub, TermList t, TermList sort)
{
  CALL("HOLUnification::postprocess");

  // ignore the sub that has been passed in, since
  // that contains substitutions formed during tree traversal which
  // are not helpful here (but cannot be erased either!)
  static RobSubstitutionTL subst;
  subst.reset();

  TypedTermList res = ToBank(RESULT_BANK).toBank(TypedTermList(t,sort));

  // this unification must pass, otherwise we wouldn't have reached a leaf  
  // however, we are forced to recompute it here with the new substitution (not ideal)
  ALWAYS(sub->unify(_origQuerySort,res.sort())); 
  return unifiers(_origQuery, res, &subst, false);    
}

bool HOLUnification::associate(unsigned specialVar, TermList node, RobSubstitutionTL* sub)
{
  CALL("HOLUnification::associate");

  TermList query(specialVar, /* special */ true);
  return unifyWithPlaceholders(query, node, sub);
}

// see E prover code by Petar /TERMS/cte_fixpoint_unif.c
#define DEBUG_FP_UNIFY(LVL, ...) if (LVL <= 0) DBG(__VA_ARGS__)
HOLUnification::OracleResult HOLUnification::fixpointUnify(TermList var, TermList t, RobSubstitutionTL* sub)
{
  CALL("HOLUnification::fixpointUnify");

  TermList v;
  // var can be an eta expanded var due to the normalisation of lambda prefixes
  // that takes place in iterator above
  if(!var.isEtaExpandedVar(v)) return OracleResult::OUT_OF_FRAGMENT;
  var = v; // set var to its eta-reduced variant

  struct TermListFP {
    TermList t;
    bool underFlex;
    unsigned depth;
  };

  bool tIsLambda = t.whnfDeref(sub).isLambdaTerm();
  TermList toFind = sub->root(var);
  TermList ts = sub->derefBound(t); // TODO do we even need this derefBound? Shouldn't t already be dereferenced???
  if(ts.isVar()) {
    DEBUG_FP_UNIFY(1, ".fp binding(", toFind, " -> ", ts, ")")
    sub->bind(toFind, ts);
    return OracleResult::SUCCESS;
  }


  Recycled<Stack<TermListFP>> todo;
  todo->push(TermListFP { .t = t, .underFlex = false, .depth = 0,  });

  while (todo->isNonEmpty()){
    auto ts = todo->pop();
    auto term = ts.t.whnfDeref(sub);
    unsigned d = ts.depth;

    // TODO consider adding an encountered store similar to first-order occurs check...

    TermList head;
    TermStack args;

    while(term.isLambdaTerm()){
      term = term.lambdaBody();
      d++;
    }

    ApplicativeHelper::getHeadAndArgs(term, head, args);

    ASS(!head.isLambdaTerm());
    if (head.isVar()) {
      if(head == toFind) {
        if(ts.underFlex || (tIsLambda && args.size())){
          return OracleResult::OUT_OF_FRAGMENT;
        } else {
          return OracleResult::FAILURE;          
        }
      }
    }

    if(head.deBruijnIndex().isSome()){
      unsigned index = head.deBruijnIndex().unwrap();
      if(index >= d){
        // contains a free index, cannot bind
        if(ts.underFlex){
          return OracleResult::OUT_OF_FRAGMENT;
        } else {
          return OracleResult::FAILURE;
        }
      }
    }

    bool argsUnderFlex = head.isVar() ? true : ts.underFlex;

    for(unsigned i = 0; i < args.size(); i++){
      todo->push(TermListFP { args[i], .underFlex = argsUnderFlex, .depth = d, } );      
    }
  }

  DEBUG_FP_UNIFY(1, ".fp binding(", toFind, " -> ", ts, ")")
  sub->bind(toFind, ts);
  return OracleResult::SUCCESS;
}


#define DEBUG_UNIFY(LVL, ...) if (LVL <= 0) DBG(__VA_ARGS__)
bool HOLUnification::unifyWithPlaceholders(TermList t1, TermList t2, RobSubstitutionTL* sub)
{
  CALL("HOLUnification::unifyWithPlaceholders");

  // TODO deal with the case where both terms are fully first-order...

  DEBUG_UNIFY(1, ".unify(", t1, ",", t2, ")")
  if(t1 == t2) {
    return true;
  }

  auto impl = [&]() -> bool {

    Recycled<Stack<UnifConstraint>> toDo;
    toDo->push(UnifConstraint(t1, t2));
    
    // Save encountered unification pairs to avoid
    // recomputing their unification
    Recycled<DHSet<UnifConstraint>> encountered;

    auto pushTodo = [&](auto pair) {
        if (!encountered->find(pair)) {
          encountered->insert(pair.clone());
          toDo->push(std::move(pair));
        }
    };

    while (toDo->isNonEmpty()) {
      auto x = toDo->pop();
      auto dt1 = sub->derefBound(x.lhs());
      auto dt2 = sub->derefBound(x.rhs());
      DEBUG_UNIFY(2, ".unify(", dt1, ",", dt2, ")")

      if (dt1 == dt2 || dt1.isPlaceholder() || dt2.isPlaceholder()) {
        // do nothing
        // we want unification to pass in these cases
      } else if(dt1.isVar() && !sub->occurs(dt1, dt2)) {
        sub->bind(dt1, dt2);
      } else if(dt2.isVar() && !sub->occurs(dt2, dt1)) {
        sub->bind(dt2, dt1);
      } else if(dt1.isTerm() && dt2.isTerm() && dt1.term()->functor() == dt2.term()->functor()) {
        
        for (unsigned i = 0; i < dt1.term()->arity(); i++) {
          pushTodo(UnifConstraint(dt1.nthArg(i), dt2.nthArg(i)));
        }

      } else {
        return false;
      }
    }
    return true;
  };

  BacktrackData localBD;
  sub->bdRecord(localBD);
  bool success = impl();
  sub->bdDone();

  if(!success) {
    localBD.backtrack();
  } else {
    if(sub->bdIsRecording()) {
      sub->bdCommit(localBD);
    }
    localBD.drop();
  }

  return success;
}

}

}

#endif