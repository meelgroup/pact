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
#include "util/random.h"
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
  std::vector<Node> tlAsserts = slv->getAssertions();
  for (Node n : tlAsserts)
  {
    expr::getSymbols(n, bvnodes_in_formula);
  }
  num_bv = bvnodes_in_formula.size();
  for (Node n : bvnodes_in_formula)
  {
    uint32_t bv_width = n.getType().getBitVectorSize();
    if ( bv_width > width) width = bv_width;
    bvnode_in_formula_v.push_back(n);
  }
  bvs_in_formula = slv->getSolver()->getVars(bvnode_in_formula_v);
  std::cout  << "[SMTApproxMC] There are " <<  num_bv <<  " bitvectors, max width = " << width <<  std::endl;
}



vector<Node> SmtApproxMc::generateNHashes(uint32_t numHashes)
{
  vector<Term> hashes;
  vector<Node> hashes_nodes;
  cvc5::Solver* solver = d_slv->getSolver();
  Assert(primes.size() >= numHashes) << "Prime size = " << primes.size() << " < numHashes = " << numHashes;
  for(uint32_t num = 0; num < numHashes; ++num)
  {
    std::string modulus = std::to_string(primes[num]);
    for(cvc5::Term x : bvs_in_formula)
    {
      std::string a_s = std::to_string(Random::getRandom().pick(1, primes[num] - 1));
      std::string b_s = std::to_string(Random::getRandom().pick(1, primes[num] - 1));
      std::string c_s = std::to_string(Random::getRandom().pick(1, primes[num] - 1));

      Sort f5 = solver->mkFiniteFieldSort(modulus);

      Term a = solver->mkFiniteFieldElem(a_s, f5);
      Term b = solver->mkFiniteFieldElem(b_s, f5);
      Term c = solver->mkFiniteFieldElem(c_s, f5);

      std::cout  << "[SMTApproxMC] Terms a (" << a_s << ") b (" << b_s << ") c (" << c_s <<  ") generated" <<  std::endl;

      Term ax = solver->mkTerm(FINITE_FIELD_MULT, {a, b});
      std::cout  << "[SMTApproxMC] Terms ax generated" <<  std::endl;

      Term axpb = solver->mkTerm(FINITE_FIELD_ADD, {ax, b});
      std::cout  << "[SMTApproxMC] Terms axpb generated" <<  std::endl;

      Term hash_const = solver->mkTerm(EQUAL, {axpb,c});

      std::cout  << "[SMTApproxMC] Terms hashc generated" <<  std::endl;

      hashes.push_back(hash_const);
    }
    hashes_nodes = solver->termVectorToNodes1(hashes);
  }
  return hashes_nodes;
}


uint64_t SmtApproxMc::smtApproxMcMain()
{
 uint32_t numIters;
 numIters = getNumIter();
 uint64_t countThisIter;


 vector<uint64_t> numList;
 populatePrimes();

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
  hashes = generateNHashes(2);
  uint64_t bound = 73;
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



