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
#include "solver_engine.h"
#include "expr/node.h"
#include "util/random.h"
#include "expr/node_converter.h"
#include "options/counting_options.h"

using std::vector;

namespace cvc5::internal {
namespace counting{

void SmtApproxMc::populatePrimes()
{
  //TODO better way to do this
  primes.push_back(17);
  primes.push_back(19);
  primes.push_back(23);
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
  Term bv_one = solver->mkBitVector(1u, 1u);

  Assert(primes.size() >= numHashes) << "Prime size = " << primes.size() << " < numHashes = " << numHashes;
  for(uint32_t num = 0; num < numHashes; ++num)
  {
    std::string modulus = std::to_string(primes[num]);
    Sort f5 = solver->mkFiniteFieldSort(modulus);

    for(uint32_t bitwidth = 0; bitwidth < width; ++bitwidth)
    {
      std::string value_here = std::to_string(int(pow(2,bitwidth)));
      ff[bitwidth] = solver->mkFiniteFieldElem(value_here, f5);
    }
    std::string b_s = std::to_string(Random::getRandom().pick(1, primes[num] - 1));
    std::string c_s = std::to_string(Random::getRandom().pick(1, primes[num] - 1));
    Term axpb = solver->mkFiniteFieldElem(b_s, f5);
    Term c = solver->mkFiniteFieldElem(c_s, f5);
    std::cout << "Adding a hash constraint (" ;
    for(cvc5::Term x : bvs_in_formula)
    {
      uint32_t num_slices = ceil(width/slice_size); //TODO (AS) consider while bitwidth non div 4

      for(uint32_t slice = 0; slice < num_slices; ++slice)
      {
        Term x_ff = solver->mkFiniteFieldElem("0", f5);

        uint32_t this_slice_start = slice*slice_size;

        std::string a_s = std::to_string(Random::getRandom().pick(1, primes[num] - 1));
        std::cout << a_s << x.getSymbol() << "[" << this_slice_start
                  << ":" << this_slice_start + slice_size - 1 << "] + " ;


        for(uint bit = this_slice_start; bit < this_slice_start + slice_size; ++bit)
        {
          Op x_bit_op = solver->mkOp(BITVECTOR_EXTRACT, {bit , bit});
          Term x_bit_bv = solver->mkTerm(x_bit_op, {x});
          Term eq_test = solver->mkTerm(EQUAL, {x_bit_bv, bv_one});
          Term ite_t = solver->mkTerm(ITE, {eq_test, ff[bit], ff[0]});

          x_ff = solver->mkTerm(FINITE_FIELD_ADD, { x_ff, ite_t });
        }


        Term a = solver->mkFiniteFieldElem(a_s, f5);
        Term ax = solver->mkTerm(FINITE_FIELD_MULT, {a, x_ff});
        axpb = solver->mkTerm(FINITE_FIELD_ADD, {ax, axpb});


      }
    }
    std::cout << b_s << ") mod " << primes[num] << " = " << c_s  << std::endl ;

    Term hash_const = solver->mkTerm(EQUAL, {axpb,c});
    hashes.push_back(hash_const);
  }
  hashes_nodes = solver->termVectorToNodes1(hashes);
  return hashes_nodes;
}


vector<Node> SmtApproxMc::generateNHashes_BV(uint32_t numHashes)
{
  vector<Term> hashes;
  vector<Node> hashes_nodes;
  cvc5::Solver* solver = d_slv->getSolver();

  Assert(primes.size() >= numHashes) << "Prime size = " << primes.size() << " < numHashes = " << numHashes;
  for(uint32_t num = 0; num < numHashes; ++num)
  {
    Sort f5 = solver->mkBitVectorSort(slice_size);


    uint32_t b_i = Random::getRandom().pick(1, primes[num] - 1);
    uint32_t c_i = Random::getRandom().pick(1, primes[num] - 1);
    uint32_t num_this_bv = 0;

    Term axpb = solver->mkBitVector(slice_size, b_i);
    Term c = solver->mkBitVector(slice_size, c_i);

    std::cout << "Adding a hash constraint (" ;

    for(cvc5::Term x : bvs_in_formula)
    {
      uint32_t this_bv_width = bvnode_in_formula_v[++num_this_bv].getType().getBitVectorSize();;
      uint32_t num_slices = ceil(this_bv_width/slice_size); //TODO (AS) consider while bitwidth non div 4

      for(uint32_t slice = 0; slice < num_slices; ++slice)
      {
        uint32_t this_slice_start = slice*slice_size;
        uint32_t this_slice_end = (slice+1)*slice_size - 1;

        uint32_t a_i = Random::getRandom().pick(1, primes[num] - 1);
        std::cout << a_i << x.getSymbol() << "[" << this_slice_start
                  << ":" << this_slice_end << "] + " ;

        Op x_bit_op = solver->mkOp(BITVECTOR_EXTRACT, {this_slice_end , this_slice_start});
        Term x_sliced = solver->mkTerm(x_bit_op, {x});
        Term a = solver->mkBitVector(slice_size, a_i);
        Term ax = solver->mkTerm(BITVECTOR_MULT, {a, x_sliced});
        axpb = solver->mkTerm(BITVECTOR_ADD, {ax, axpb});
        }
    }
    Term p = solver->mkBitVector(slice_size, primes[num]);

    axpb = solver->mkTerm(BITVECTOR_UREM, {axpb,p});

    std::cout << b_i << ") mod " << primes[num] << " = " << c_i  << std::endl ;

    Term hash_const = solver->mkTerm(EQUAL, {axpb,c});
    hashes.push_back(hash_const);
    std::cout << hash_const <<std::endl;
  }
  hashes_nodes = solver->termVectorToNodes1(hashes);

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
  vector<Node> hashes;
  int numHashes = 1;
  options::HashingMode hashtype = options::HashingMode::BV; //TODO (AS) : what's wrong with line below?
  //options::HashingMode hashtype = options().counting.hashsm;
  if(hashtype == options::HashingMode::BV)
  {
    hashes = generateNHashes_BV(numHashes);
  }
  else
  {
    Assert(hashtype == options::HashingMode::FF)
      << "Hashing method should be one of BV or FF. Given : " << hashtype << std::endl;
    hashes = generateNHashes(numHashes);

  }
  int64_t bound = 40;
  uint64_t count = 1;
  std::string ss = "";
  for (int i = 0; i < numHashes; ++i)
  {
    count *= primes[i];
    ss += "*" + std::to_string(primes[i]) ;
  }
  bound = d_slv->boundedSat(hashes, bound);
  std::cout << "SMTApproxMCCore returning count " << bound*count
            << " (" << bound << ss << ")" << std::endl;
  return bound*count;
}

template<class T>
inline T SmtApproxMc::findMedian(vector<T>& numList)
{
  Assert(!numList.empty());
  std::sort(numList.begin(), numList.end());
  size_t medIndex = numList.size() / 2;
  if (medIndex >= numList.size()) {
    return numList[numList.size() - 1];
  }
  return numList[medIndex];
}


}  // namespace counting
}  // namespace cvc5::internal



