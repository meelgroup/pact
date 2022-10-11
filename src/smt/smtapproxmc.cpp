/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * SMTApproxMC : Implementation of Approximate Model Counter with
 * word level hash functions
 */

#include "smt/smtapproxmc.h"
#include "smt/hash_generator.h"

#include <bits/stdc++.h>

namespace cvc5::internal {

SMTApproxMC::SMTApproxMC(const Options* optr)
{
  // TODO update these from command line option
  epsilon = 0.8;
  numiteration = 9;
  minPivot = 1;
  maxPivot = int(2 * ceil(4.94 * (1 + 1 / epsilon) * (1 + 1 / epsilon)));
}

uint64_t SMTApproxMC::countByEnumeration(u_int64_t limit){
  return limit; //TODO implement
}

uint64_t SMTApproxMC::smtApxInnerLoop() // "SMTApproxMCCore"
{
  u_int64_t num_solutions = 0;
  num_solutions = countByEnumeration(maxPivot);
  if (num_solutions >= maxPivot) {

  } else if (num_solutions >= minPivot) {

  } else {

  }

  return num_solutions;
}

uint64_t SMTApproxMC::smtApxOuterLoop()
{
  uint64_t count;
  std::vector<u_int64_t> counts;
  for (int i = 0; i < numiteration; i++)
  {
    count = smtApxInnerLoop();
    counts.push_back(count);
  }
  std::sort(counts.begin(), counts.end());
  count = counts[counts.size() / 2];
  return count;
}

}  // namespace cvc5::internal
