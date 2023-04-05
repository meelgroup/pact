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
#include "solver_engine.h"
#include "expr/node.h"
#include "expr/node_converter.h"

using std::vector;

namespace cvc5::internal {

void SmtApproxMc::populatePrimes()
{
  //TODO better way to do this
  primes.push_back(5);
  primes.push_back(7);
  primes.push_back(13);
}

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

SmtApproxMc::SmtApproxMc(SolverEngine* slv)
{
  this->d_slv = slv;
  width = 5;
  num_bv = 3;
  // TODO set logic -- add FF to logic
  // TODO get width, num_bv variables correctly
  // TODO list all bitvectors in use
}

void getbitvectors()
{
  TheoryEngine* te = d_smtSolver->getTheoryEngine();
  logicInfo();

}


vector<Node> SmtApproxMc::generateNHashes(uint32_t numHashes)
{
  Node oneHash;
  vector<Node> hashes;
  for(uint32_t num = 0; num < numHashes; ++num)
  {
    cvc5::Solver* solver = d_slv->getSolver();
    Assert(primes.size() >= num);
    std::string modulus = std::to_string(primes[num]);
    Sort f5 = solver->mkFiniteFieldSort(modulus);
    Term a = solver->mkConst(f5, "a");
    Term b = solver->mkConst(f5, "b");
    Term z = solver->mkFiniteFieldElem("0", f5);
    hashes.push_back(oneHash);
    Term inv =
    solver->mkTerm(EQUAL,
                  {solver->mkTerm(FINITE_FIELD_ADD,
                    {solver->mkTerm(FINITE_FIELD_MULT, {a, b}),
                                 solver->mkFiniteFieldElem("-1", f5)}),
                  z});
  }
  return hashes;
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
  std::cout << "Entering in SMTApproxMCCore" << std::endl;
  vector<Node> hashes;
  hashes = generateNHashes(1);
  uint64_t bound = 10073;
  d_slv->boundedSat(hashes, bound);
  return bound;
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


}  // namespace cvc5::internal



