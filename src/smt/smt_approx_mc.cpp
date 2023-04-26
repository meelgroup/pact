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
  primes.push_back(2);//0
  primes.push_back(2);//1
  primes.push_back(5);//2
  primes.push_back(11);//3
  primes.push_back(17);//4
  primes.push_back(37);//5
  primes.push_back(67);//6
  primes.push_back(131);//7
  primes.push_back(257);//8
  primes.push_back(521);//9
  primes.push_back(1031);//10
  primes.push_back(2053);//11
  primes.push_back(4099);//12
  primes.push_back(8209);//13
  primes.push_back(16411);//14
  primes.push_back(32771);//15
  primes.push_back(65537);//16
  primes.push_back(131101);//17
  primes.push_back(262147);//18
  primes.push_back(524309);//19
  primes.push_back(1048583);//20
  primes.push_back(2097169);//21
  primes.push_back(4194319);//22
  primes.push_back(8388617);//23
  primes.push_back(16777259);//24
  primes.push_back(33554467);//25
  primes.push_back(67108879);//26
  primes.push_back(134217757);//27
  primes.push_back(268435459);//28
  primes.push_back(536870923);//29
  primes.push_back(1073741827);//30
  primes.push_back(2147483659);//31
  primes.push_back(4294967311);//32
  primes.push_back(8589934609);//33
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
  slice_size = slv->getOptions().counting.slicesize;
  std::cout  << "[SMTApproxMC] There are " <<  num_bv <<  " bitvectors, max width = " << width
             << " Slice size = " << slice_size << std::endl;
  verb = slv->getOptions().counting.countingverb;
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
     if (verb > 0) std::cout << "Adding a hash constraint (" ;
    for(cvc5::Term x : bvs_in_formula)
    {
      uint32_t num_slices = ceil(width/slice_size);

      for(uint32_t slice = 0; slice < num_slices; ++slice)
      {
        Term x_ff = solver->mkFiniteFieldElem("0", f5);

        uint32_t this_slice_start = slice*slice_size;

        std::string a_s = std::to_string(Random::getRandom().pick(1, primes[num] - 1));
        if (verb > 0)
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
     if (verb > 0)
      std::cout << b_s << ") mod " << primes[num] << " = " << c_s  << std::endl ;

    Term hash_const = solver->mkTerm(EQUAL, {axpb,c});
    hashes.push_back(hash_const);
  }
  hashes_nodes = solver->termVectorToNodes1(hashes);
  return hashes_nodes;
}


Term SmtApproxMc::generate_hash()
{
  cvc5::Solver* solver = d_slv->getSolver();

  uint32_t new_bv_width = slice_size + 1;

  Sort f5 = solver->mkBitVectorSort(new_bv_width);

  Term p = solver->mkBitVector(new_bv_width, primes[slice_size]);

  uint32_t b_i = Random::getRandom().pick(1, primes[slice_size] - 1);
  uint32_t c_i = Random::getRandom().pick(1, primes[slice_size] - 1);
  uint32_t num_this_bv = 0;

  Term axpb = solver->mkBitVector(new_bv_width, b_i);
  Term c = solver->mkBitVector(new_bv_width, c_i);

  if (verb > 0) std::cout << "Adding a hash constraint (" ;

  for(cvc5::Term x : bvs_in_formula)
  {
    uint32_t this_bv_width = bvnode_in_formula_v[num_this_bv++].getType().getBitVectorSize();;
    uint32_t num_slices = ceil(this_bv_width/slice_size);

    for(uint32_t slice = 0; slice < num_slices; ++slice)
    {
      uint32_t this_slice_start = slice*slice_size;
      uint32_t this_slice_end = (slice+1)*slice_size - 1;
      if (this_slice_end >= this_bv_width)
        this_slice_end = this_bv_width - 1;

      uint32_t a_i = Random::getRandom().pick(1, primes[slice_size] - 1);
      if (verb > 0)
        std::cout << a_i << x.getSymbol() << "[" << this_slice_start
                << ":" << this_slice_end << "] + " ;

      Op x_bit_op = solver->mkOp(BITVECTOR_EXTRACT, {this_slice_end , this_slice_start});
      Term x_sliced = solver->mkTerm(x_bit_op, {x});
      Op x_zero_ex_op = solver->mkOp(BITVECTOR_ZERO_EXTEND, {1});
      x_sliced = solver->mkTerm(x_zero_ex_op, {x_sliced});
      Term a = solver->mkBitVector(new_bv_width, a_i);
      Term ax = solver->mkTerm(BITVECTOR_MULT, {a, x_sliced});
      ax = solver->mkTerm(BITVECTOR_UREM, {ax,p});
      axpb = solver->mkTerm(BITVECTOR_ADD, {ax, axpb});
      }
  }

    axpb = solver->mkTerm(BITVECTOR_UREM, {axpb,p});
    if (verb > 0)
      std::cout << b_i << ") mod " << primes[slice_size] << " = " << c_i  << std::endl ;

    Term hash_const = solver->mkTerm(EQUAL, {axpb,c});

  return hash_const;
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
   if (countThisIter == 0){
     iter--;
     std::cout << "[Round " << iter << "] failing count " << std::endl;
   } else {
   std::cout << "[Round " << iter << "] returning count " << countThisIter << std::endl;
     numList.push_back(countThisIter);
  }
 }
 countThisIter = findMedian(numList);
 return countThisIter;
}

uint64_t SmtApproxMc::smtApproxMcCore()
{
  vector<Node> hashes;
  Term hash;
  int numHashes = 1, oldhashes = 0;
  int growingphase = 1;
  int lowbound = 1, highbound = 2, bsatcall = 0;
  int nochange = 0;

  int64_t bound = getPivot();
  uint64_t count = bound;
  std::string ss = "";

  while(true){
    if (numHashes > oldhashes){
      if (verb > 0) std::cout << "Pushing Hashes : " << numHashes - oldhashes << std::endl;
      for(int i = oldhashes; i < numHashes;  ++i){
        d_slv->getSolver()->push();
        hash = generate_hash();
        d_slv->getSolver()->assertFormula(hash);
      }
      oldhashes = numHashes;
    } else if (numHashes < oldhashes) {
      if (verb > 0) std::cout << "Poping Hashes : " <<  oldhashes - numHashes << std::endl;
      d_slv->getSolver()->pop(oldhashes - numHashes);
      oldhashes = numHashes;
    } else {
      if (verb > 0) std::cout << "Strange! No change in num hashes!" << std::endl;
    }
    count = d_slv->boundedSat(hashes, bound);

    std::cout << "[BoundedSat] call " << ++bsatcall << " numHashes = "
            << numHashes << " count = " << count
            << " ( bound = " << bound << ")" << std::endl;


    if (count == 0) {
      growingphase = 0;
      lowbound = numHashes/2; highbound = numHashes - 1;
    } else if (count < bound){
      if (verb > 0) std::cout << "Poping Hashes : " <<  oldhashes << std::endl;
      d_slv->getSolver()->pop(oldhashes);
      break;
    }

    if (growingphase){
      numHashes *= 2;
    } else {
      nochange = 0;
      if (highbound < lowbound){
        if (verb > 0) std::cout << "Poping Hashes : " <<  oldhashes << std::endl;
        d_slv->getSolver()->pop(oldhashes);
        break;
      }
      else if (count == bound){
        if (lowbound == numHashes) nochange = 1;
        lowbound = numHashes;
      }
      else if (count == 0){
        if (highbound == numHashes) nochange = 1;
        highbound = numHashes;
      }
      else{
        if (verb > 0) std::cout << "Poping Hashes : " <<  oldhashes << std::endl;
        d_slv->getSolver()->pop(oldhashes);
        break;
      }
      if(nochange){
        if (verb > 0) std::cout << "Poping Hashes : " <<  oldhashes << std::endl;
        d_slv->getSolver()->pop(oldhashes);
        return 0;
      }
      numHashes = ceil((lowbound+highbound)/2);
    }

  }

  for (int i = 0; i < numHashes; ++i)
  {
    count *= primes[slice_size];
  }
  return count;
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



