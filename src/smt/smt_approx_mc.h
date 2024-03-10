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
  int numHashes = 0, oldhashes = 0;
  vector<uint64_t> primes;
  std::unordered_set<Node> bvnodes_in_formula;
  std::vector<Node> bvnode_in_formula_v, projection_vars;
  std::vector<Term> bvs_in_projset, booleans_in_projset;
  std::vector<Term> bvs_in_formula, vars_in_formula, booleans_in_formula;
  Term ff[100];
  int verb = 0;
  std::string projection_prefix;
  bool project_on_booleans = true;
  bool get_projected_count = false;
  std::vector<Term> projection_var_terms;

 public:
  SmtApproxMc(SolverEngine* slv);
  virtual ~SmtApproxMc() {}

  void populatePrimes();
  vector<Node> generateNHashes(uint32_t numHashes);
  Term generate_boolean_hash();
  Term generate_hash();
  Term generate_integer_hash(uint32_t hash_num);
  uint64_t smtApproxMcMain();
  uint64_t getMinBW();
  uint64_t smtApproxMcCore();
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
