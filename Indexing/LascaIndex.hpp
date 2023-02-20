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
 * @file LascaIndex.hpp
 * Defines class LascaIndex
 *
 */

#ifndef __LASCA_LascaIndex__
#define __LASCA_LascaIndex__


#include "Kernel/LASCA.hpp"

#include "Indexing/IndexManager.hpp"
#include "Indexing/TermIndex.hpp"
#include "Indexing/Index.hpp"
#include "Indexing/TermSubstitutionTree.hpp"

#define DEBUG(...) // DBG(__VA_ARGS__)

namespace Indexing {

template<class T>
class LascaIndex : public Indexing::Index
{
public:
  CLASS_NAME(LascaIndex);
  USE_ALLOCATOR(LascaIndex);

  LascaIndex(Shell::Options::UnificationWithAbstraction uwa)
    : _index(uwa)
    , _shared()
  {}

  void setShared(shared_ptr<Kernel::LascaState> shared) { _shared = std::move(shared); }

  auto find(TypedTermList key)
  {
    CALL("LascaIndex::find")
    return iterTraits(_index.getUwa(key))
      .map([](auto r) { return std::make_tuple(std::move(r.data()), r.unifier);  })
      // .filter([=](auto& x) {
      //     Stack<UnificationConstraint> c;
      //     MismatchHandler hndlr(_uwa, c);
      //     auto& uwa = get<1>(x);
      //     auto result = uwa.cnstLiterals()
      //       .all([&](auto lit) {
      //           ASS(lit->isEquality() && lit->isNegative())
      //           auto l = lit->termArg(0);
      //           auto r = lit->termArg(1);
      //           return l == r || hndlr.checkUWA(l,r);
      //       });
      //     if (!result) { DEBUG("skipping wrong constraints: ", uwa) }
      //     ASS(c.isEmpty());
      //     return result;
      // })
      .timeTraced(_lookupStr.c_str()); }


  auto generalizations(TermList key, bool retrieveSubstitutions = true)
  { return iterTraits(_index.getGeneralizations(key, retrieveSubstitutions)); }

  auto instances(TermList key, bool retrieveSubstitutions = true)
  { return iterTraits(_index.getInstances(key, retrieveSubstitutions)); }

  virtual void handleClause(Clause* c, bool adding) final override
  {
    CALL("LascaIndex::handleClause")
    TIME_TRACE(_maintainanceStr.c_str())
    for (auto appl : T::iter(*_shared, c)) {
      if (adding) {
        auto k = appl.key();
        _index.insert(std::move(appl));
        ASS_REP(find(k).hasNext(), k)
      } else {
        _index.remove(std::move(appl));
      }
    }
  }

private:
  TermSubstitutionTree<T> _index;
  shared_ptr<Kernel::LascaState> _shared;
  static vstring _lookupStr;
  static vstring _maintainanceStr;
};

template<class T> vstring LascaIndex<T>::_lookupStr = T::name() + vstring(" lookup");
template<class T> vstring LascaIndex<T>::_maintainanceStr = T::name() + vstring(" maintainance");

} // namespace Indexing

#undef DEBUG

#endif // __LASCA_LascaIndex__