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

#include <vector>

#include "cvc5_private.h"

#ifndef CVC5__SMT__APXMC_H
#define CVC5__SMT__APXMC_H

#include "expr/node_algorithm.h"
#include "smt/env_obj.h"
#include "util/statistics_stats.h"

using std::vector;

namespace cvc5::internal {
namespace counting {

class SmtApproxMc;

class SmtApproxMc
{
 private:
  SolverEngine* d_slv;
  uint32_t max_bitwidth = 0, num_bv = 0, num_bool = 0;
  uint32_t num_floats = 0, num_real = 0, num_integer = 0;
  uint32_t num_bv_projset = 0, num_bool_projset = 0;
  uint32_t slice_size = 2;
  uint32_t threshold = 0, measurements = 0;
  int numHashes = 0, oldhashes = 0, olderhashes = 0;
  vector<uint64_t> primes;
  vector<uint64_t> num_hash_list;
  vector<double> num_count_list;
  std::unordered_set<Node> bvnodes_in_formula;
  std::vector<Node> bvnode_in_formula_v, projection_vars;
  std::vector<Term> bvs_in_projset, booleans_in_projset;
  std::vector<Term> bvs_in_formula, vars_in_formula, booleans_in_formula;
  Term ff[100];
  int verb = 0;
  std::string projection_prefix;
  bool project_on_booleans = true;
  bool get_projected_count = false;
  bool two_factor_prime = true;
  std::vector<Term> projection_var_terms;
  int64_t count;

  // The following things in this file needs to be reinitialized for each
  // iteration of the SMTApproxMC core loop

  // Tells the number of solutions found at hash number N
  // sols_for_hash[N] tells the number of solutions found when N hashes were
  // added
  std::map<uint64_t, int64_t> sols_for_hash;

  int64_t lower_fib = 0;
  int64_t upper_fib = 0;
  int64_t hash_cnt = 0;
  int64_t hash_prev = 0;
  int64_t total_max_hashes = 0;
  int64_t num_explored = 0;
  int64_t prev_measure = 0;  // TODO AS : ApproxMC did not have this
  int64_t iter = 0;

  // threshold_sols[hash_num]==1 tells us that at hash_num number of hashes
  // there were found to be FULL threshold number of solutions
  // threshold_sols[hash_num]==0 tells that there were less than threshold
  // number of solutions.
  // if it's not set, we have no clue.
  std::map<uint64_t, bool> threshold_sols;

 public:
  SmtApproxMc(SolverEngine* slv);
  virtual ~SmtApproxMc() {}

  void populatePrimes();
  vector<Node> generateNHashes(uint32_t numHashes);
  Term generate_boolean_hash();
  Term generate_hash(uint32_t bitwidth = 0);
  void set_up_probs_threshold_measurements();
  uint64_t two_factor_check(uint slice_size);
  double calc_error_bound(uint32_t t, double p);
  Term generate_integer_hash(uint32_t hash_num);
  Term generate_lemire_hash(uint32_t hash_num);
  void init_iteration_data();
  uint64_t smtApproxMcMain();
  uint64_t getMinBW();
  uint64_t getMinBWlemire();
  uint64_t smtApproxMcCore();
  int64_t getNextIndex(uint64_t prev_index,
                       uint64_t prev_prev_index,
                       uint64_t count,
                       bool start_of_iter);
  uint32_t getPivot();
  vector<Node>& get_projection_nodes();
  uint32_t getNumIter();
  template <class T>
  T findMedian(vector<T>& numList);
  double getTime();
};

}  // namespace counting
}  // namespace cvc5::internal
#endif
