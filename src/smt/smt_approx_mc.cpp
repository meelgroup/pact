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

// clang-format off
#include <cvc5/cvc5.h>
#include <cvc5/cvc5_export.h>
#include <math.h>

#include "expr/node.h"
#include "expr/node_converter.h"
#include "options/counting_options.h"
#include "smt/smt_approx_mc.h"
#include "solver_engine.h"
#include "util/random.h"
// clang-format on

using std::vector;

namespace cvc5::internal {
namespace counting {

void SmtApproxMc::populatePrimes()
{
  primes = {2,          2,          5,          11,        17,        37,
            67,         131,        257,        521,       1031,      2053,
            4099,       8209,       16411,      32771,     65537,     131101,
            262147,     524309,     1048583,    2097169,   4194319,   8388617,
            16777259,   33554467,   67108879,   134217757, 268435459, 536870923,
            1073741827, 2147483659, 4294967311, 8589934609};
}

uint32_t SmtApproxMc::getPivot()
{
  double epsilon = 0.8;
  uint32_t pivot;
  pivot = int(2 * ceil(4.49 * pow((1 + 1 / epsilon), 2)));
  return pivot;
}

uint32_t SmtApproxMc::getNumIter()
{
  double delta = 2.5;
  return int(ceil(25 * log(3 / delta)));
}

/**
 * Minimum Bitwidth needed for the hashing constraint
 * to avoid overflow.
 */

SmtApproxMc::SmtApproxMc(SolverEngine* slv)
{
  this->d_slv = slv;
  std::vector<Node> tlAsserts = slv->getAssertions();

  projection_prefix = slv->getOptions().counting.projprefix;
  get_projected_count = slv->getOptions().counting.projcount;

  for (Node n : tlAsserts)
  {
    expr::getSymbols(n, bvnodes_in_formula);
    for (Node nx : bvnodes_in_formula)
    {
      bvnode_in_formula_v.push_back(nx);
    }
  }
  vars_in_formula = slv->getSolver()->getVars(bvnode_in_formula_v);

  vector<std::string> var_list;
  for (Term n : vars_in_formula)
  {
    bool in_projset =
        (n.getSymbol().compare(0, projection_prefix.size(), projection_prefix)
         == 0);

    if (std::find(var_list.begin(), var_list.end(), n.getSymbol())
        != var_list.end())
      continue;
    else
      var_list.push_back(n.getSymbol());

    if (n.getSort().isBitVector())
    {
      num_bv++;
      bvs_in_formula.push_back(n);
      if (n.getSort().getBitVectorSize() > max_bitwidth)
        max_bitwidth = n.getSort().getBitVectorSize();
      if (in_projset || !get_projected_count)
      {
        num_bv_projset++;
        bvs_in_projset.push_back(n);
      }
    }
    else if (n.getSort().isBoolean())
    {
      num_bool++;
      booleans_in_formula.push_back(n);
      if (in_projset || !get_projected_count)
      {
        num_bool_projset++;
        booleans_in_projset.push_back(n);
      }
    }
    else if (n.getSort().isFloatingPoint())
    {
      num_floats++;
    }
    else if (n.getSort().isReal())
    {
      num_real++;
    }
    else if (n.getSort().isInteger())
    {
      num_integer++;
    }
  }

  if (num_bv_projset == 0 && num_bool_projset > 0)
    project_on_booleans = true;
  else
    project_on_booleans = false;

  projection_var_terms = bvs_in_projset;
  projection_var_terms.insert(projection_var_terms.end(),
                              booleans_in_projset.begin(),
                              booleans_in_projset.end());

  projection_vars = slv->getSolver()->termVectorToNodes1(projection_var_terms);

  slice_size = slv->getOptions().counting.slicesize;
  if (slice_size == 0) slice_size = max_bitwidth / 2;
  if (slice_size > max_bitwidth) slice_size = max_bitwidth;
  if (slice_size > 32) slice_size = 16;
  verb = slv->getOptions().counting.countingverb;

  std::cout << "c [smtappmc] formula spec: Booleans: " << num_bool
            << " bitvectors: " << num_bv << " max width = " << max_bitwidth
            << std::endl
            << "c [smtappmc] Reals: " << num_real << " FPs: " << num_floats
            << " Integers: " << num_integer << std::endl
            << "c [smtappmc] Sampling set: Booleans: " << num_bool_projset
            << " bitvectors: " << num_bv_projset << std::endl;
}

Term SmtApproxMc::generate_boolean_hash()
{
  cvc5::Solver* solver = d_slv->getSolver();
  Term xorcons = solver->mkBoolean(Random::getRandom().pick(0, 1));
  for (cvc5::Term x : booleans_in_projset)
  {
    Assert(x.getSort().isBoolean());
    if (Random::getRandom().pick(0, 1) == 1)
    {
      xorcons = solver->mkTerm(XOR, {xorcons, x});
    }
  }
  return xorcons;
}

uint64_t SmtApproxMc::getMinBW()
{
  uint32_t min_bw = 2 * slice_size + 1;
  uint32_t num_sliced_var = 0;
  for (cvc5::Term x : bvs_in_projset)
  {
    uint32_t this_bv_width = x.getSort().getBitVectorSize();
    uint32_t num_slices = (this_bv_width + slice_size - 1) / slice_size;
    num_sliced_var += num_slices;
  }
  uint32_t extension_for_sum =
      static_cast<uint32_t>(std::ceil(std::log(num_sliced_var) / std::log(2)));

  min_bw += extension_for_sum;
  // std::cout << "extending " << slice_size << " bits to " << slice_size +
  // min_bw << std::endl;

  return min_bw;
}

Term SmtApproxMc::generate_integer_hash(uint32_t hash_num)
{
  cvc5::Solver* solver = d_slv->getSolver();
  uint32_t new_bv_width = getMinBW();

  Term p = solver->mkBitVector(new_bv_width, primes[slice_size]);

  uint32_t c_i = Random::getRandom().pick(0, primes[slice_size] - 1);

  Term axpb = solver->mkBitVector(new_bv_width, 0);
  Term one = solver->mkBitVector(new_bv_width, 1);
  Term maxx = solver->mkBitVector(new_bv_width, pow(2, slice_size + 1));
  Term c = solver->mkBitVector(new_bv_width, c_i);

  Sort bvsort = solver->mkBitVectorSort(new_bv_width);
  std::string var_name = "hash" + std::to_string(hash_num);
  Term new_var = solver->mkConst(bvsort, var_name);
  projection_var_terms.push_back(new_var);
  projection_vars =
      d_slv->getSolver()->termVectorToNodes1(projection_var_terms);
  Term new_var_mult_p = solver->mkTerm(BITVECTOR_MULT, {new_var, p});
  Term new_var_plusone = solver->mkTerm(BITVECTOR_ADD, {new_var, one});
  Term new_var_plusone_mult_p =
      solver->mkTerm(BITVECTOR_MULT, {new_var_plusone, p});
  Term hash_const_less = solver->mkTerm(BITVECTOR_ULT, {new_var, maxx});
  c = solver->mkTerm(BITVECTOR_ADD, {c, new_var_mult_p});

  Trace("smap-hash") << pow(2, slice_size) << "Adding Hash: (";

  for (cvc5::Term x : bvs_in_projset)
  {
    uint32_t this_bv_width = x.getSort().getBitVectorSize();
    uint32_t num_slices = ceil(this_bv_width / slice_size);
    if (slice_size > this_bv_width) num_slices = 1;
    for (uint32_t slice = 0; slice < num_slices; ++slice)
    {
      uint32_t this_slice_start = slice * slice_size;
      uint32_t this_slice_end = (slice + 1) * slice_size - 1;
      uint extend_x_by_bits = 2 + slice_size;
      if (this_slice_end >= this_bv_width)
      {
        extend_x_by_bits = this_slice_end - this_bv_width + 3 + slice_size;
        this_slice_end = this_bv_width - 1;
      }
      uint32_t a_i = Random::getRandom().pick(0, primes[slice_size] - 1);
      Trace("smap-hash") << a_i << x.getSymbol() << "[" << this_slice_start
                         << ":" << this_slice_end << "] + ";

      Op x_bit_op =
          solver->mkOp(BITVECTOR_EXTRACT, {this_slice_end, this_slice_start});
      Term x_sliced = solver->mkTerm(x_bit_op, {x});
      Op x_zero_ex_op = solver->mkOp(BITVECTOR_ZERO_EXTEND, {extend_x_by_bits});
      x_sliced = solver->mkTerm(x_zero_ex_op, {x_sliced});
      Term a = solver->mkBitVector(new_bv_width, a_i);
      Term ax = solver->mkTerm(BITVECTOR_MULT, {a, x_sliced});
      axpb = solver->mkTerm(BITVECTOR_ADD, {ax, axpb});
    }
  }

  Trace("smap-hash") << " 0) = " << primes[slice_size] << "h" << hash_num
                     << " + " << c_i << "\n";

  Term hash_const = solver->mkTerm(EQUAL, {axpb, c});
  //   hash_const_less =
  //     solver->mkTerm(BITVECTOR_ULE, {c,maxx});
  Trace("smap-print-hash") << "\n"
                           << "(assert " << hash_const << ")"
                           << "\n";
  hash_const = solver->mkTerm(AND, {hash_const, hash_const_less});
  Trace("smap-print-hash") << "\n"
                           << "(assert " << hash_const_less << ")"
                           << "\n";
  Trace("smap-print-hash") << "\n"
                           << "(assert " << hash_const << ")"
                           << "\n";

  return hash_const;
}

Term SmtApproxMc::generate_lemire_hash(uint32_t hash_num)
{
  cvc5::Solver* solver = d_slv->getSolver();

  // new_bv_width is the bitwidth of ax term which is 2w
  uint32_t new_bv_width = slice_size * 2;

  uint32_t c_i = Random::getRandom().pick(0, pow(2, slice_size) - 1);

  Term axpb = solver->mkBitVector(new_bv_width, 0);
  Term c = solver->mkBitVector(slice_size, c_i);

  Sort bvsort = solver->mkBitVectorSort(new_bv_width);
  std::string var_name = "hash" + std::to_string(hash_num);
  Term new_var = solver->mkConst(bvsort, var_name);
  projection_var_terms.push_back(new_var);
  projection_vars =
      d_slv->getSolver()->termVectorToNodes1(projection_var_terms);

  Trace("smap-hash") << pow(2, slice_size) << "Adding Hash: (";

  for (cvc5::Term x : bvs_in_projset)
  {
    uint32_t this_bv_width = x.getSort().getBitVectorSize();
    uint32_t num_slices = ceil(this_bv_width / slice_size);
    if (slice_size > this_bv_width) num_slices = 1;
    for (uint32_t slice = 0; slice < num_slices; ++slice)
    {
      uint32_t this_slice_start = slice * slice_size;
      uint32_t this_slice_end = (slice + 1) * slice_size - 1;
      uint extend_x_by_bits = slice_size;
      if (this_slice_end >= this_bv_width)
      {
        extend_x_by_bits = this_slice_end - this_bv_width + slice_size - 1;
        this_slice_end = this_bv_width - 1;
      }
      uint32_t a_i = Random::getRandom().pick(0, primes[slice_size] - 1);
      Trace("smap-hash") << a_i << x.getSymbol() << "[" << this_slice_start
                         << ":" << this_slice_end << "] + ";
      Trace("smap") << "adding slicing operator\n";
      Op x_bit_op =
          solver->mkOp(BITVECTOR_EXTRACT, {this_slice_end, this_slice_start});
      Term x_sliced = solver->mkTerm(x_bit_op, {x});
      Op x_zero_ex_op = solver->mkOp(BITVECTOR_ZERO_EXTEND, {extend_x_by_bits});
      x_sliced = solver->mkTerm(x_zero_ex_op, {x_sliced});
      Term a = solver->mkBitVector(new_bv_width, a_i);
      Trace("smap") << "adding multiplication operator" << new_bv_width << " "
                    << extend_x_by_bits + slice_size << "\n";
      Term ax = solver->mkTerm(BITVECTOR_MULT, {a, x_sliced});
      Trace("smap") << "adding addition operator\n";
      axpb = solver->mkTerm(BITVECTOR_ADD, {ax, axpb});
    }
  }

  Trace("smap") << "adding div operarion\n";

  Op axpb_div_op =
      solver->mkOp(BITVECTOR_EXTRACT, {slice_size * 2 - 1, slice_size});
  Trace("smap") << "creating div term\n";
  Term axpb_div = solver->mkTerm(axpb_div_op, {axpb});
  Trace("smap-hash") << " 0) = " << primes[slice_size] << "h" << hash_num
                     << " + " << c_i << "\n";
  Trace("smap") << "creating equal term\n";

  Term hash_const = solver->mkTerm(EQUAL, {axpb_div, c});

  Trace("smap-print-hash") << "\n"
                           << "(assert " << hash_const << ")"
                           << "\n";

  return hash_const;
}

Term SmtApproxMc::generate_hash()
{
  cvc5::Solver* solver = d_slv->getSolver();

  uint32_t new_bv_width = getMinBW();

  Term p = solver->mkBitVector(new_bv_width, primes[slice_size]);

  uint32_t c_i = Random::getRandom().pick(0, primes[slice_size] - 1);

  Term axpb = solver->mkBitVector(new_bv_width, 0);
  Term c = solver->mkBitVector(new_bv_width, c_i);

  Trace("smap-hash") << "Adding a hash constraint (size "
                     << bvs_in_formula.size() << ") : (";

  for (cvc5::Term x : bvs_in_projset)
  {
    uint32_t this_bv_width = x.getSort().getBitVectorSize();
    uint32_t num_slices = ceil(this_bv_width / slice_size);
    if (slice_size > this_bv_width)
    {
      num_slices = 1;
    }
    for (uint32_t slice = 0; slice < num_slices; ++slice)
    {
      uint32_t this_slice_start = slice * slice_size;
      uint32_t this_slice_end = (slice + 1) * slice_size - 1;
      uint32_t extend_x_by_bits = new_bv_width - slice_size;

      // If slicesize does not divide bv width, and this is last
      // slice, then extend this slice more than others
      if (this_slice_end >= this_bv_width)
      {
        extend_x_by_bits =
            this_slice_end - this_bv_width + 1 + new_bv_width - slice_size;
        this_slice_end = this_bv_width - 1;
      }

      uint32_t a_i = Random::getRandom().pick(0, primes[slice_size] - 1);
      Trace("smap-hash") << a_i << x.getSymbol() << "[" << this_slice_start
                         << ":" << this_slice_end << "] + ";

      Op x_bit_op =
          solver->mkOp(BITVECTOR_EXTRACT, {this_slice_end, this_slice_start});
      Term x_sliced = solver->mkTerm(x_bit_op, {x});
      Op x_zero_ex_op = solver->mkOp(BITVECTOR_ZERO_EXTEND, {extend_x_by_bits});
      x_sliced = solver->mkTerm(x_zero_ex_op, {x_sliced});
      Term a = solver->mkBitVector(new_bv_width, a_i);
      Term ax = solver->mkTerm(BITVECTOR_MULT, {a, x_sliced});
      // ax = solver->mkTerm(BITVECTOR_UREM, {ax,p});
      axpb = solver->mkTerm(BITVECTOR_ADD, {ax, axpb});
    }
  }

  axpb = solver->mkTerm(BITVECTOR_UREM, {axpb, p});
  Trace("smap-hash") << " 0) mod " << primes[slice_size] << " = " << c_i
                     << "\n";

  Term hash_const = solver->mkTerm(EQUAL, {axpb, c});
  Trace("smap-print-hash") << "chash "
                           << "(assert " << hash_const << ")"
                           << "\n";

  return hash_const;
}

uint64_t SmtApproxMc::smtApproxMcMain()
{
  uint32_t numIters;
  numIters = getNumIter();
  uint64_t countThisIter;

  vector<uint64_t> numList;
  populatePrimes();

  for (uint32_t iter = 1; iter <= numIters; ++iter)
  {
    countThisIter = smtApproxMcCore();
    if (countThisIter == 0 && numHashes > 0)
    {
      std::cout << "c [smtappmc] [ " << getTime()
                << "] completed round: " << iter << "] failing count "
                << std::endl;
      iter--;
    }
    else
    {
      std::cout << "c [smtappmc] [ " << getTime()
                << "] completed round: " << iter << " count: " << countThisIter
                << std::endl;
      numList.push_back(countThisIter);
    }
    if (numHashes == 0) break;
  }
  countThisIter = findMedian(numList);
  std::cout << "c Total time : " << getTime() << std::endl;
  return countThisIter;
}

double SmtApproxMc::getTime()
{
  std::stringstream s;
  std::string time_str1;
  s << d_slv->getSolver()->getStatistics().get("global::totalTime");
  s >> time_str1;
  time_str1.resize(time_str1.size() - 2);
  const std::string time_str = time_str1;
  double time_int = std::stod(time_str) / 1000.0;
  return time_int;
}

vector<Node>& SmtApproxMc::get_projection_nodes() { return projection_vars; }

uint64_t SmtApproxMc::smtApproxMcCore()
{
  Term hash;
  int growingphase = 1;
  int lowbound = 1, highbound = 2;
  int nochange = 0;
  oldhashes = 0;

  int64_t bound = getPivot();
  int64_t count = bound;
  std::string ss = "";

  while (true)
  {
    if (numHashes > oldhashes)
    {
      Trace("smap") << "Pushing Hashes : " << numHashes - oldhashes << "\n";
      for (int i = oldhashes; i < numHashes; ++i)
      {
        d_slv->getSolver()->push();
        if (project_on_booleans && get_projected_count)
          hash = generate_boolean_hash();
        else if (d_slv->getOptions().counting.hashsm
                 == options::HashingMode::BV)
          hash = generate_hash();
        else if (d_slv->getOptions().counting.hashsm
                 == options::HashingMode::LEM)
        {
          hash = generate_lemire_hash(i);
        }
        else
        {
          Assert(d_slv->getOptions().counting.hashsm
                 == options::HashingMode::INT);
          hash = generate_integer_hash(i);
        }
        d_slv->getSolver()->assertFormula(hash);
      }
      oldhashes = numHashes;
    }
    else if (numHashes < oldhashes)
    {
      Trace("smap") << "Poping Hashes : " << oldhashes - numHashes << "\n";
      d_slv->getSolver()->pop(oldhashes - numHashes);
      if (d_slv->getOptions().counting.hashsm == options::HashingMode::INT)
      {
        for (int i = 0; i < oldhashes - numHashes; i++)
        {
          projection_var_terms.pop_back();  // TODO (AS) making no sense now
        }
        projection_vars =
            d_slv->getSolver()->termVectorToNodes1(projection_var_terms);
      }

      oldhashes = numHashes;
    }
    else
    {
      Trace("smap") << "Strange! No change in num hashes!"
                    << "\n";
    }

    std::cout << "c [smtappmc] [ " << getTime()
              << "] bounded_sol_count looking for " << bound
              << " solutions -- hashes active: " << numHashes << std::endl;

    count = d_slv->boundedSat(bound, numHashes, projection_vars);

    std::cout << "c [smtappmc] [ " << getTime() << "] got solutions: " << count
              << " out of " << bound << std::endl;

    if (count == 0)
    {
      growingphase = 0;
      lowbound = numHashes / 2;
      highbound = numHashes - 1;
    }
    else if (count < bound)
    {
      if (verb > 0) std::cout << "Poping Hashes : " << oldhashes << std::endl;
      d_slv->getSolver()->pop(oldhashes);
      if (d_slv->getOptions().counting.hashsm == options::HashingMode::INT)
      {
        for (int i = 0; i < oldhashes; i++)
        {
          projection_var_terms.pop_back();
        }
        projection_vars =
            d_slv->getSolver()->termVectorToNodes1(projection_var_terms);
      }
      break;
    }

    if (growingphase)
    {
      numHashes *= 2;
      if (numHashes == 0) numHashes = 1;
    }
    else
    {
      nochange = 0;
      if (highbound < lowbound)
      {
        Trace("smap") << "Poping Hashes : " << oldhashes << "\n";
        d_slv->getSolver()->pop(oldhashes);
        break;
      }
      else if (count == bound)
      {
        if (lowbound == numHashes) nochange = 1;
        lowbound = numHashes;
      }
      else if (count == 0)
      {
        if (highbound == numHashes) nochange = 1;
        highbound = numHashes;
      }
      else
      {
        Trace("smap") << "Poping Hashes : " << oldhashes << "\n";
        d_slv->getSolver()->pop(oldhashes);
        break;
      }
      if (nochange)
      {
        Trace("smap") << "Poping Hashes : " << oldhashes << "\n";
        d_slv->getSolver()->pop(oldhashes);
        return 0;
      }
      numHashes = ceil((lowbound + highbound) / 2);
    }
  }

  for (int i = 0; i < numHashes; ++i)
  {
    if (project_on_booleans)
      count *= 2;
    else if (d_slv->getOptions().counting.hashsm == options::HashingMode::LEM)
      count *= pow(2, slice_size);
    else
      count *= primes[slice_size];
  }
  return count;
}

template <class T>
inline T SmtApproxMc::findMedian(vector<T>& numList)
{
  Assert(!numList.empty());
  std::sort(numList.begin(), numList.end());
  size_t medIndex = numList.size() / 2;
  if (medIndex >= numList.size())
  {
    return numList[numList.size() - 1];
  }
  return numList[medIndex];
}

vector<Node> SmtApproxMc::generateNHashes(uint32_t numhashes)
{
  vector<Term> hashes;
  vector<Node> hashes_nodes;
  cvc5::Solver* solver = d_slv->getSolver();
  Term bv_one = solver->mkBitVector(1u, 1u);

  Assert(primes.size() >= numHashes)
      << "Prime size = " << primes.size() << " < numHashes = " << numhashes;
  for (uint32_t num = 0; num < numhashes; ++num)
  {
    std::string modulus = std::to_string(primes[num]);
    Sort f5 = solver->mkFiniteFieldSort(modulus);

    for (uint32_t bitwidth = 0; bitwidth < max_bitwidth; ++bitwidth)
    {
      std::string value_here = std::to_string(int(pow(2, bitwidth)));
      ff[bitwidth] = solver->mkFiniteFieldElem(value_here, f5);
    }
    std::string b_s =
        std::to_string(Random::getRandom().pick(1, primes[num] - 1));
    std::string c_s =
        std::to_string(Random::getRandom().pick(1, primes[num] - 1));
    Term axpb = solver->mkFiniteFieldElem(b_s, f5);
    Term c = solver->mkFiniteFieldElem(c_s, f5);
    if (verb > 0) std::cout << "Adding a hash constraint (";
    for (cvc5::Term x : bvs_in_formula)
    {
      uint32_t num_slices = ceil(max_bitwidth / slice_size);

      for (uint32_t slice = 0; slice < num_slices; ++slice)
      {
        Term x_ff = solver->mkFiniteFieldElem("0", f5);

        uint32_t this_slice_start = slice * slice_size;

        std::string a_s =
            std::to_string(Random::getRandom().pick(1, primes[num] - 1));
        if (verb > 0)
          std::cout << a_s << x.getSymbol() << "[" << this_slice_start << ":"
                    << this_slice_start + slice_size - 1 << "] + ";

        for (uint bit = this_slice_start; bit < this_slice_start + slice_size;
             ++bit)
        {
          Op x_bit_op = solver->mkOp(BITVECTOR_EXTRACT, {bit, bit});
          Term x_bit_bv = solver->mkTerm(x_bit_op, {x});
          Term eq_test = solver->mkTerm(EQUAL, {x_bit_bv, bv_one});
          Term ite_t = solver->mkTerm(ITE, {eq_test, ff[bit], ff[0]});

          x_ff = solver->mkTerm(FINITE_FIELD_ADD, {x_ff, ite_t});
        }

        Term a = solver->mkFiniteFieldElem(a_s, f5);
        Term ax = solver->mkTerm(FINITE_FIELD_MULT, {a, x_ff});
        axpb = solver->mkTerm(FINITE_FIELD_ADD, {ax, axpb});
      }
    }
    if (verb > 0)
      std::cout << b_s << ") mod " << primes[num] << " = " << c_s << std::endl;

    Term hash_const = solver->mkTerm(EQUAL, {axpb, c});
    hashes.push_back(hash_const);
  }
  hashes_nodes = solver->termVectorToNodes1(hashes);
  return hashes_nodes;
}

}  // namespace counting
}  // namespace cvc5::internal
