/******************************************************************************
 * Top contributors (to current version):
 *   Arijit Shaw
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Word-level function generator.
 *
 * Implementation Hash function generator needed for counting with SMTApproxMC.
 */

#include <cvc5/cvc5.h>
#include <cvc5/cvc5_export.h>
#include "smt/smt_approx_mc.h"

#include <math.h>
#include <cassert>

namespace cvc5::internal {
namespace smt {

uint32_t SmtApproxMc::getPivot()
{
  double epsilon = 0.8;
  uint32_t pivot;
  pivot  = int(2*ceil(4.49* pow((1+ 1/epsilon),2)));
  return pivot;
}

uint32_t SmtApproxMc::getNumIter()
{
  double delta = 2.5;
  return int(ceil(25*log(3/delta)));
}

uint64_t SmtApproxMc::smtApproxMcMain()
{
 uint32_t numIters;
 numIters = getNumIter();
 uint64_t countThisIter;
 vector<uint64_t> numList;
 for (uint32_t iter = 0 ; iter <= numIters; ++iter )
 {
   countThisIter = smtApproxMcCore();
   numList.push_back(countThisIter);
 }
 countThisIter = findMedian(numList);
 return countThisIter;
}

uint64_t SmtApproxMc::smtApproxMcCore()
{

}

template<class T>
inline T SmtApproxMc::findMedian(vector<T>& numList)
{
  assert(!numList.empty());
  std::sort(numList.begin(), numList.end());
  size_t medIndex = numList.size() / 2;
  if (medIndex >= numList.size()) {
    return numList[numList.size() - 1];
  }
  return numList[medIndex];
}


}  // namespace smt
}  // namespace cvc5::internal



