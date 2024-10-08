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
#include <map>

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
  two_factor_prime = slv->getOptions().counting.twofactorprime;

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
      if (d_slv->getOptions().counting.listint)
      {
        bvs_in_projset.push_back(n);
        std::cout << "c [smtappmc] Integer variable in projection set: "
                  << n.getSymbol() << std::endl;
      }
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
  if (d_slv->getOptions().counting.listint)
  {
    std::cout << "c [smtappmc] Number of varibales "
              << projection_var_terms.size() << std::endl;
  }
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

uint64_t SmtApproxMc::getMinBW(int bitwidth = 0)
{
  if (d_slv->getOptions().counting.hashsm == options::HashingMode::ASH)
    return bitwidth;
  else if (d_slv->getOptions().counting.lessbw)
    return bitwidth + 2;
  uint32_t min_bw = 2 * slice_size + 1;
  uint32_t num_sliced_var = 0;
  if (bitwidth == 0) bitwidth = slice_size;

  for (cvc5::Term x : bvs_in_projset)
  {
    uint32_t this_bv_width = x.getSort().getBitVectorSize();
    uint32_t num_slices = (this_bv_width + bitwidth - 1) / bitwidth;
    num_sliced_var += num_slices;
  }
  uint32_t extension_for_sum =
      static_cast<uint32_t>(std::ceil(std::log(num_sliced_var) / std::log(2)));

  min_bw += extension_for_sum;
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
                           << "(assert " << hash_const << ")" << "\n";
  hash_const = solver->mkTerm(AND, {hash_const, hash_const_less});
  Trace("smap-print-hash") << "\n"
                           << "(assert " << hash_const_less << ")" << "\n";
  Trace("smap-print-hash") << "\n"
                           << "(assert " << hash_const << ")" << "\n";

  return hash_const;
}

Term SmtApproxMc::generate_ashwin_hash(uint32_t bitwidth)
{
  cvc5::Solver* solver = d_slv->getSolver();
  uint32_t a_i;

  uint32_t c_i = Random::getRandom().pick(0, pow(2, bitwidth) - 1);

  Term axpb = solver->mkBitVector(bitwidth, 0);
  Term c = solver->mkBitVector(bitwidth, c_i);

  Sort bvsort = solver->mkBitVectorSort(bitwidth);

  projection_vars =
      d_slv->getSolver()->termVectorToNodes1(projection_var_terms);

  Trace("smap-hash") << "Adding Hash: (";

  for (cvc5::Term x : bvs_in_projset)
  {
    uint32_t this_bv_width = x.getSort().getBitVectorSize();
    uint32_t num_slices = ceil(this_bv_width / bitwidth);
    if (bitwidth > this_bv_width) num_slices = 1;
    for (uint32_t slice = 0; slice < num_slices; ++slice)
    {
      uint32_t this_slice_start = slice * bitwidth;
      uint32_t this_slice_end = (slice + 1) * bitwidth - 1;
      if (this_slice_end >= this_bv_width)
      {
        this_slice_end = this_bv_width - 1;
      }
      if (bitwidth == 1)
        a_i = Random::getRandom().pick(0, pow(2, bitwidth) - 1);  // * 2 + 1;
      else
        a_i = Random::getRandom().pick(0, pow(2, bitwidth - 1) - 1) * 2 + 1;

      Trace("smap-hash") << a_i << x.getSymbol() << "[" << this_slice_start
                         << ":" << this_slice_end << "] + ";
      Trace("smap") << "adding slicing operator\n";
      Op x_bit_op =
          solver->mkOp(BITVECTOR_EXTRACT, {this_slice_end, this_slice_start});
      Term x_sliced = solver->mkTerm(x_bit_op, {x});
      Term a = solver->mkBitVector(bitwidth, a_i);
      Term ax = solver->mkTerm(BITVECTOR_MULT, {a, x_sliced});
      Trace("smap") << "adding addition operator\n";
      axpb = solver->mkTerm(BITVECTOR_ADD, {ax, axpb});
    }
  }

  Trace("smap") << "adding div operarion\n";

  Trace("smap-hash") << " 0) = " << c_i << "\n";
  Trace("smap") << "creating equal term\n";

  Term hash_const = solver->mkTerm(EQUAL, {axpb, c});
  Trace("smap-print-hash") << "\n"
                           << "(assert " << hash_const << ")" << "\n";
  return hash_const;
}

Term SmtApproxMc::generate_lemire_hash(uint32_t bitwidth)
{
  uint32_t a_i;
  cvc5::Solver* solver = d_slv->getSolver();

  // new_bv_width is the bitwidth of ax term which is 2w
  uint32_t new_bv_width = bitwidth * 2;

  uint32_t c_i = Random::getRandom().pick(0, pow(2, bitwidth) - 1);

  Term axpb = solver->mkBitVector(new_bv_width, 0);
  Term c = solver->mkBitVector(bitwidth, c_i);

  Sort bvsort = solver->mkBitVectorSort(new_bv_width);
  // std::string var_name = "hash" + std::to_string(hash_num);
  // Term new_var = solver->mkConst(bvsort, var_name);
  // projection_var_terms.push_back(new_var);
  projection_vars =
      d_slv->getSolver()->termVectorToNodes1(projection_var_terms);

  Trace("smap-hash") << pow(2, bitwidth) << "Adding Hash: (";

  for (cvc5::Term x : bvs_in_projset)
  {
    uint32_t this_bv_width = x.getSort().getBitVectorSize();
    uint32_t num_slices = ceil(this_bv_width / bitwidth);
    if (bitwidth > this_bv_width) num_slices = 1;
    for (uint32_t slice = 0; slice < num_slices; ++slice)
    {
      uint32_t this_slice_start = slice * bitwidth;
      uint32_t this_slice_end = (slice + 1) * bitwidth - 1;
      uint extend_x_by_bits = bitwidth;
      if (this_slice_end >= this_bv_width)
      {
        extend_x_by_bits = this_slice_end - this_bv_width + bitwidth - 1;
        this_slice_end = this_bv_width - 1;
      }
      a_i = Random::getRandom().pick(0, pow(2, 2 * bitwidth) - 1);
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
                    << extend_x_by_bits + bitwidth << "\n";
      Term ax = solver->mkTerm(BITVECTOR_MULT, {a, x_sliced});
      Trace("smap") << "adding addition operator\n";
      axpb = solver->mkTerm(BITVECTOR_ADD, {ax, axpb});
    }
  }

  Trace("smap") << "adding div operarion\n";

  Op axpb_div_op =
      solver->mkOp(BITVECTOR_EXTRACT, {bitwidth * 2 - 1, bitwidth});
  Trace("smap") << "creating div term\n";
  Term axpb_div = solver->mkTerm(axpb_div_op, {axpb});
  Trace("smap-hash") << " 0) = " << primes[bitwidth] << " + " << c_i << "\n";
  Trace("smap") << "creating equal term\n";

  Term hash_const = solver->mkTerm(EQUAL, {axpb_div, c});

  Trace("smap-print-hash") << "\n"
                           << "(assert " << hash_const << ")" << "\n";

  return hash_const;
}

Term SmtApproxMc::generate_hash(uint32_t bitwidth = 0)
{
  if (bitwidth == 0) bitwidth = slice_size;
  Trace("smap-hash") << "Generating hash for bitwidth " << bitwidth << "\n";
  Assert(bitwidth > 0) << "Bitwidth should be greater than 0";
  cvc5::Solver* solver = d_slv->getSolver();

  uint32_t new_bv_width = getMinBW(bitwidth);

  Term p = solver->mkBitVector(new_bv_width, primes[bitwidth]);

  uint32_t c_i = Random::getRandom().pick(0, primes[bitwidth] - 1);

  Term axpb = solver->mkBitVector(new_bv_width, 0);
  Term c = solver->mkBitVector(new_bv_width, c_i);

  Trace("smap-hash") << "Adding a hash constraint (size "
                     << bvs_in_formula.size() << ") : (";

  for (cvc5::Term x : bvs_in_projset)
  {
    uint32_t this_bv_width = x.getSort().getBitVectorSize();
    uint32_t num_slices = ceil(this_bv_width / bitwidth);
    if (bitwidth > this_bv_width)
    {
      num_slices = 1;
    }
    for (uint32_t slice = 0; slice < num_slices; ++slice)
    {
      uint32_t this_slice_start = slice * bitwidth;
      uint32_t this_slice_end = (slice + 1) * bitwidth - 1;
      uint32_t extend_x_by_bits = new_bv_width - bitwidth;

      // If slicesize does not divide bv width, and this is last
      // slice, then extend this slice more than others
      if (this_slice_end >= this_bv_width)
      {
        extend_x_by_bits =
            this_slice_end - this_bv_width + 1 + new_bv_width - bitwidth;
        this_slice_end = this_bv_width - 1;
      }

      uint32_t a_i = Random::getRandom().pick(0, primes[bitwidth] - 1);
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
  Trace("smap-hash") << " 0) mod " << primes[bitwidth] << " = " << c_i << "\n";

  Term hash_const = solver->mkTerm(EQUAL, {axpb, c});
  Trace("smap-print-hash") << "chash " << "(assert " << hash_const << ")"
                           << "\n";

  return hash_const;
}

double SmtApproxMc::calc_error_bound(uint32_t t, double p)
{
  double curr = pow(p, t);
  double sum = curr;
  for (auto k = t - 1; k >= std::ceil(double(t) / 2); k--)
  {
    curr *= double((k + 1)) / (t - k) * (1 - p) / p;
    sum += curr;
  }

  return sum;
}

uint64_t SmtApproxMc::two_factor_check(uint slice)
{
  uint64_t bound = getPivot() + 1, multiplier = 1;
  uint32_t i = 1;
  uint64_t bounded_sat_count = 1, last_count = 1;
  Term hash;
  for (i = slice; i > 0; i--)
  {
    if (d_slv->getOptions().counting.hashsm == options::HashingMode::ASH)
    {
      hash = generate_ashwin_hash(i);
      multiplier = pow(2, i + 1);
    }
    else if (d_slv->getOptions().counting.hashsm == options::HashingMode::BV)
    {
      hash = generate_hash(i);
      multiplier = primes[i + 1];
    }
    else if (d_slv->getOptions().counting.hashsm == options::HashingMode::LEM)
    {
      hash = generate_lemire_hash(i);
      multiplier = pow(2, i + 1);
    }
    Trace("smap") << "Pushing Hashes : " << 1 << "\n";

    d_slv->getSolver()->push();
    d_slv->getSolver()->assertFormula(hash);
    bounded_sat_count = d_slv->boundedSat(bound, 0, projection_vars);
    Trace("pact-tfc") << "Count at " << i << " is " << bounded_sat_count
                      << "\n";
    if (bounded_sat_count >= bound)
    {
      Trace("smap") << "Poping Hashes : " << 1 << "\n";
      d_slv->getSolver()->pop(1);
      Trace("pact-tfc") << "Count is grater than bound at " << i
                        << ", breaking, popped\n";
      break;
    }
    Trace("smap") << "Poping Hashes : " << 1 << "\n";
    d_slv->getSolver()->pop(1);
    last_count = bounded_sat_count;
  }

  Trace("pact-tfc") << "should multiply by " << multiplier * last_count << "\n";
  std::cout << "c [smtappmc] [ " << getTime()
            << "] two-factor check: last prime is " << multiplier << std::endl;
  return multiplier * last_count;
}

void SmtApproxMc::set_up_probs_threshold_measurements()
{
  int best_match = -1;
  double thresh_factor;

  if (best_match != -1)
  {
    thresh_factor = 1.1;
  }
  else
  {
    thresh_factor = 1.0;
  }

  double epsilon = d_slv->getOptions().counting.epsilon;
  double delta = d_slv->getOptions().counting.delta;

  threshold = int(1
                  + thresh_factor * 9.84 * (1.0 + (1.0 / epsilon))
                        * (1.0 + (1.0 / epsilon))
                        * (1.0 + (epsilon / (1.0 + epsilon))));

  Trace("smap") << "[smtap] threshold set to " << threshold << "\n";

  double p_L = 0;
  if (epsilon < sqrt(2) - 1)
  {
    p_L = 0.262;
  }
  else if (epsilon < 1)
  {
    p_L = 0.157;
  }
  else if (epsilon < 3)
  {
    p_L = 0.085;
  }
  else if (epsilon < 4 * sqrt(2) - 1)
  {
    p_L = 0.055;
  }
  else
  {
    p_L = 0.023;
  }

  double p_U = 0;
  if (epsilon < 3)
  {
    p_U = 0.169;
  }
  else
  {
    p_U = 0.044;
  }

  for (measurements = 1;; measurements += 2)
  {
    if (calc_error_bound(measurements, p_L)
            + calc_error_bound(measurements, p_U)
        <= delta)
    {
      break;
    }
  }
}

uint64_t SmtApproxMc::smtApproxMcMain()
{
  uint32_t numIters;
  numIters = getNumIter();
  uint64_t countThisIter;

  vector<uint64_t> numList;
  populatePrimes();

  for (iter = 0; iter < numIters; ++iter)
  {
    countThisIter = smtApproxMcCore();
    prev_measure = hash_cnt;
    // if (countThisIter == 0 && numHashes > 0)
    // {
    //   std::cout << "c [smtappmc] [ " << getTime()
    //             << "] completed round: " << iter << "] failing count "
    //             << std::endl;
    //   iter--;
    // }
    // else
    // {
    std::cout << "c [smtappmc] [ " << getTime() << "] completed round: " << iter
              << " count: " << countThisIter << std::endl;
    numList.push_back(countThisIter);
    // }
    if (exact_count == true)
    {
      std::cout << "c [smtappmc] [ " << getTime()
                << "] terminating as exact count is found" << std::endl;
      break;
    }
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

// Return next index to look at for count, negative denotes that we have found
// the count in the last iteration, done
int64_t SmtApproxMc::getNextIndex(uint64_t prev_index,
                                  uint64_t prev_prev_index,
                                  uint64_t count_i,
                                  bool start_of_iter)
{
  hash_cnt = prev_index;
  hash_prev = prev_prev_index;
  bool is_first_iter = false;

  if (count_i == threshold + 1)
  {
    threshold_sols[hash_cnt] = 1;
    Trace("pact-getnext") << "Threshold solutions found at " << hash_cnt
                          << "\n";
  }
  else
  {
    threshold_sols[hash_cnt] = 0;
    Trace("pact-getnext") << "Threshold solutions not found at " << hash_cnt
                          << "\n";
  }

  // We are doing a galloping search here (see our IJCAI-16 paper for more
  // details). lowerFib is referred to as loIndex and upperFib is referred to as
  // hiIndex The key idea is that we first do an exponential search and then do
  // binary search This is implemented by using two sentinels: lowerFib and
  // upperFib. The correct answer
  //  is always between lowFib and upperFib. We do exponential search until
  //  upperFib < lowerFib/2 Once upperFib < lowerFib/2; we do a binary search.
  // while (num_explored < total_max_hashes)
  // {

  if (lower_fib == 0 && upper_fib == total_max_hashes && hash_cnt == 0)
  {
    Assert(prev_index == 0);
    Trace("pact-getnext") << "getNextIndex returning 0 as first iteration\n";
    upper_fib = total_max_hashes - 1;
    is_first_iter = true;
    if (prev_measure != 0)
    {
      Assert(prev_measure != 0) << "prev_measure is 0, which is unlikely";
      Trace("pact-getnext")
          << "Returning prev_measure " << prev_measure << "\n";
    }
  }

  uint64_t cur_hash_cnt = hash_cnt;
  // prev_measure = prev_index;  // TODO AS : not sure

  const uint64_t num_sols = std::min<uint64_t>(count, threshold + 1);
  Assert(num_sols <= threshold + 1);
  // bool found_full = (num_sols == threshold + 1);

  if (num_sols < threshold + 1)
  {
    num_explored = lower_fib + total_max_hashes - hash_cnt;
    Trace("pact-getnext") << "Found " << num_sols << " solutions at "
                          << hash_cnt << "threshold " << threshold << "\n";

    // one less hash count had threshold solutions
    // this one has less than threshold
    // so this is the real deal!
    if (hash_cnt == 0
        || (threshold_sols.find(hash_cnt - 1) != threshold_sols.end()
            && threshold_sols[hash_cnt - 1] == 1))
    {
      num_hash_list.push_back(hash_cnt);
      num_count_list.push_back(num_sols);
      prev_measure = hash_cnt;
      Trace("pact-getnext")
          << "Found winner (595)" << num_sols << " solutions at " << hash_cnt
          << prev_measure << "\n";
      return -(hash_cnt);
    }

    threshold_sols[hash_cnt] = 0;
    sols_for_hash[hash_cnt] = num_sols;

    Trace("pact-getnext") << "At this point " << prev_measure << " " << hash_cnt
                          << " " << upper_fib << " " << iter << "\n";
    if (std::abs(hash_cnt - prev_measure) <= 2)
    {
      // Doing linear, this is a re-count
      upper_fib = hash_cnt;
      hash_cnt--;
      Trace("pact-getnext") << "Linear search recount : " << lower_fib << " "
                            << hash_cnt << " " << upper_fib << "\n";
    }
    else
    {
      if (hash_prev > hash_cnt) hash_prev = 0;
      upper_fib = hash_cnt;
      if (hash_prev > lower_fib) lower_fib = hash_prev;
      hash_cnt = (upper_fib + lower_fib) / 2;
      Trace("pact-getnext")
          << "Binary search (found < threshold): " << lower_fib << " "
          << hash_cnt << " " << upper_fib << "\n";
    }
  }
  else
  {
    Assert(num_sols == threshold + 1);
    Trace("pact-getnext") << "Found full solutions at " << hash_cnt << "\n";
    num_explored = hash_cnt + total_max_hashes - upper_fib;

    // success record for +1 hashcount exists and is 0
    // so one-above hashcount was below threshold, this is above
    // we have a winner -- the one above!
    if (threshold_sols.find(hash_cnt + 1) != threshold_sols.end()
        && threshold_sols[hash_cnt + 1] == 0 && !is_first_iter)
    {
      num_hash_list.push_back(hash_cnt + 1);
      num_count_list.push_back(sols_for_hash[hash_cnt + 1]);
      prev_measure = hash_cnt + 1;
      Trace("pact-getnext")
          << "Found winner (617)" << sols_for_hash[hash_cnt + 1]
          << " solutions at " << hash_cnt + 1 << "\n";
      return -(hash_cnt + 1);
    }

    threshold_sols[hash_cnt] = 1;
    sols_for_hash[hash_cnt] = threshold + 1;
    if (iter > 0 && std ::abs(hash_cnt - prev_measure) < 2)
    {
      // Doing linear, this is a re-count
      lower_fib = hash_cnt;
      hash_cnt++;
      Trace("pact-getnext") << "Linear search: " << lower_fib << " " << hash_cnt
                            << " " << upper_fib << "\n";
    }
    else if (lower_fib + (hash_cnt - lower_fib) * 2 >= upper_fib - 1)
    {
      // Whenever the above condition is satisfied, we are in binary search
      // mode
      lower_fib = hash_cnt;
      hash_cnt = (lower_fib + upper_fib) / 2;
      Trace("pact-getnext") << "Binary search: " << lower_fib << " " << hash_cnt
                            << " " << upper_fib << "\n";
    }
    else
    {
      // We are in exponential search mode.
      const auto old_hash_cnt = hash_cnt;
      hash_cnt = lower_fib + (hash_cnt - lower_fib) * 2;
      if (old_hash_cnt == hash_cnt) hash_cnt++;
      Trace("pact-getnext")
          << "Exponential search: " << lower_fib << " " << old_hash_cnt << " "
          << upper_fib << " " << hash_cnt << "\n";
    }
  }
  Trace("pact-getnext") << "Returning hash count: " << hash_cnt << "\n";
  hash_prev = cur_hash_cnt;
  if (is_first_iter)
  {
    if (prev_measure != 0)
      return prev_measure;
    else
      return 0;
  }
  return hash_cnt;
}
void SmtApproxMc::init_iteration_data()
{
  num_hash_list.clear();
  num_count_list.clear();
  threshold_sols.clear();
  sols_for_hash.clear();
  // TODO AS max hashes is not the right term here
  total_max_hashes = projection_vars.size()
                     * 32;  // should be getmaxBW or something complicated
  lower_fib = 0;
  upper_fib = total_max_hashes;
  hash_cnt = 0;
  hash_prev = 0;

  threshold = getPivot();
  count = threshold + 1;
  // TODO AS remember to add the actual constant generation routine
  threshold_sols[total_max_hashes] = 0;
  sols_for_hash[total_max_hashes] = 1;
}

uint64_t SmtApproxMc::smtApproxMcCore()
{
  Term hash;
  numHashes = 0, oldhashes = 0, olderhashes = 0;

  int64_t bound = getPivot();
  std::string ss = "";
  uint64_t final_count = 0, old_count = 42;

  bool start_of_iter = true;
  init_iteration_data();

  while (true)
  {
    numHashes = getNextIndex(oldhashes, olderhashes, count, start_of_iter);
    Trace("pact-getnext") << "Next hash to check boudedsat = " << numHashes
                          << " last checked:" << oldhashes << "\n";
    start_of_iter = false;
    if (numHashes < 0)
    {
      if (!two_factor_prime)
      {
        if (abs(numHashes) == oldhashes)
        {
          final_count = count;
        }
        else
        {
          final_count = old_count;
          Assert(abs(numHashes) == oldhashes + 1);
        }
        numHashes = abs(numHashes);
        break;
      }
      Trace("pact-tfc") << "Count at " << 1 << " is " << count << "\n";
      if (abs(numHashes) == oldhashes)
      {
        Trace("pact-tfc") << "new = old case, pop 1\n";
        d_slv->getSolver()->pop(1);
      }
      else
      {
        Trace("pact-tfc") << "new = old + 1 case, no pop\n";
        Assert(abs(numHashes) == oldhashes + 1);
      }
      final_count = two_factor_check(slice_size);
      Trace("pact-tfc") << "count returned by tfc is " << final_count << "\n";
      if (abs(numHashes) == oldhashes)
      {
        // this is a fake push just to keep the pop stack consistent
        Trace("smap") << "Pushing Hashes : " << 1 << "\n";
        d_slv->getSolver()->push();
      }
      numHashes = abs(numHashes) - 1;
      break;
    }

    if (numHashes > oldhashes)
    {
      Trace("smap") << "Pushing Hashes : " << numHashes - oldhashes << "\n";
      for (int i = oldhashes; i < numHashes; ++i)
      {
        d_slv->getSolver()->push();
        if (project_on_booleans && get_projected_count)
          hash = generate_boolean_hash();
        else if (d_slv->getOptions().counting.hashsm
                 == options::HashingMode::ASH)
          hash = generate_ashwin_hash(slice_size);
        else if (d_slv->getOptions().counting.hashsm
                 == options::HashingMode::BV)
          hash = generate_hash(slice_size);
        else if (d_slv->getOptions().counting.hashsm
                 == options::HashingMode::LEM)
        {
          hash = generate_lemire_hash(slice_size);
        }
        else
        {
          Assert(d_slv->getOptions().counting.hashsm
                 == options::HashingMode::INT);
          hash = generate_integer_hash(i);
        }
        d_slv->getSolver()->assertFormula(hash);
      }
      // prev_measure = oldhashes;
      olderhashes = oldhashes;
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
      // prev_measure = oldhashes;
      olderhashes = oldhashes;
      oldhashes = numHashes;
    }
    else
    {
      Trace("smap") << "No change in num hashes! This should not happen\n";
    }

    std::cout << "c [smtappmc] [ " << getTime()
              << "] bounded_sol_count looking for " << bound + 1
              << " solutions -- hashes active: " << numHashes << std::endl;

    old_count = count;
    count = d_slv->boundedSat(bound + 1, numHashes, projection_vars);

    std::cout << "c [smtappmc] [ " << getTime() << "] got solutions: " << count
              << " out of " << bound + 1 << std::endl;
    if (count >= bound || numHashes > 0)
    {
      exact_count = false;
    }
    else
    {
      std::cout << "c [smtappmc] [ " << getTime()
                << "] terminating as exact count is found" << std::endl;
      final_count = count;
      break;
    }
  }

  Trace("pact-tfc") << "Count returned is " << final_count << "*"
                    << primes[slice_size] << "^" << numHashes << "\n";

  for (int i = 0; i < numHashes; ++i)
  {
    if (project_on_booleans)
      count *= 2;
    else if (d_slv->getOptions().counting.hashsm == options::HashingMode::LEM)
      final_count *= pow(2, slice_size);
    else
      final_count *= primes[slice_size];
  }
  Trace("smap") << "Poping Hashes : " << oldhashes << "\n";

  d_slv->getSolver()->pop(oldhashes);
  return final_count;
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

  Assert(primes.size() >= (uint64_t)numHashes)
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
