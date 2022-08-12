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
 * Wrapper for ApproxMC Model Counter
 *
 * Implementation of the  ApproxMC Model Counter for cvc5 (bit-vectors).
 */

#include "prop/approxmc.h"

#ifdef CVC5_USE_APPROXMC

#include <approxmc.h>
#include <bits/stdc++.h>

#include "base/check.h"
#include "util/resource_manager.h"
#include "util/statistics_registry.h"

namespace cvc5::internal {
namespace prop {

// using ApxMCVar = unsigned;
using ApproxMCVar = unsigned;

// helper functions
namespace {

CMSat::Lit toInternalLit(SatLiteral lit)
{
  if (lit == undefSatLiteral)
  {
    return CMSat::lit_Undef;
  }
  return CMSat::Lit(lit.getSatVariable(), lit.isNegated());
}

void toInternalClause(SatClause& clause,
                      std::vector<CMSat::Lit>& internal_clause)
{
  for (unsigned i = 0; i < clause.size(); ++i)
  {
    internal_clause.push_back(toInternalLit(clause[i]));
  }
  Assert(clause.size() == internal_clause.size());
}

}  // namespace

ApproxMCounter::ApproxMCounter(StatisticsRegistry& registry,
                               const std::string& name)
    : d_counter(new ApproxMC::AppMC()),
      d_numVariables(0),
      d_okay(true),
      d_statistics(registry, name),
      d_resmgr(nullptr)
{
}

void ApproxMCounter::init()
{
  std::cout << "ApproxMC Init called" << std::endl;

  d_true = newVar();
  d_false = newVar();

  std::vector<CMSat::Lit> clause(1);
  clause[0] = CMSat::Lit(d_true, false);
  d_counter->add_clause(clause);

  clause[0] = CMSat::Lit(d_false, true);
  d_counter->add_clause(clause);
}

ApproxMCounter::~ApproxMCounter() {}

ClauseId ApproxMCounter::addXorClause(SatClause& clause,
                                      bool rhs,
                                      bool removable)
{
  Trace("sat::cryptominisat")
      << "Add xor clause " << clause << " = " << rhs << "\n";

  if (!d_okay)
  {
    Trace("sat::cryptominisat") << "Solver unsat: not adding clause.\n";
    return ClauseIdError;
  }

  ++(d_statistics.d_xorClausesAdded);

  // ensure all sat literals have positive polarity by pushing
  // the negation on the result
  std::vector<ApproxMCVar> xor_clause;
  for (unsigned i = 0; i < clause.size(); ++i)
  {
    xor_clause.push_back(toInternalLit(clause[i]).var());
    rhs ^= clause[i].isNegated();
  }
  d_counter->add_xor_clause(xor_clause, rhs);

  return ClauseIdError;
}

ClauseId ApproxMCounter::addClause(SatClause& clause, bool removable)
{
  Trace("sat::cryptominisat") << "Add clause " << clause << "\n";

  if (!d_okay)
  {
    Trace("sat::cryptominisat") << "Solver unsat: not adding clause.\n";
    return ClauseIdError;
  }

  ++(d_statistics.d_clausesAdded);

  std::vector<CMSat::Lit> internal_clause;
  toInternalClause(clause, internal_clause);
  d_counter->add_clause(internal_clause);

  ClauseId freshId;
  freshId = ClauseIdError;

  return freshId;
}

bool ApproxMCounter::ok() const { return d_okay; }

SatVariable ApproxMCounter::newVar(bool isTheoryAtom,
                                   bool preRegister,
                                   bool canErase)
{
  d_counter->new_var();
  ++d_numVariables;
  Assert(d_numVariables == d_counter->nVars());
  return d_numVariables - 1;
}

SatVariable ApproxMCounter::trueVar() { return d_true; }

SatVariable ApproxMCounter::falseVar() { return d_false; }

void ApproxMCounter::interrupt()
{
  Unreachable() << "Not sure how to interrupt in ApproxMC";
}

SatValue ApproxMCounter::solve()
{
  std::cout << "ApproxMC called" << std::endl;
  TimerStat::CodeTimer codeTimer(d_statistics.d_solveTime);
  ++d_statistics.d_statCallsToSolve;
  d_counter->set_verbosity(0);
  ApproxMC::SolCount solcount = d_counter->count();
  // d_counter->print_stats(0);  //TODO may be turned on, along with
  // set_verbosity
  std::cout << "[ApproxMC] Count = " << solcount.cellSolCount << "*2**"
            << solcount.hashCount << std::endl;
  std::cout << "s mc "
            << (long long int)(solcount.cellSolCount
                               * (long long int)pow(2, solcount.hashCount))
            << std::endl;
  return SAT_VALUE_UNKNOWN;
}

SatValue ApproxMCounter::solve(long unsigned int& resource)
{
  // ApproxMC::SalverConf conf = d_counter->getConf();
  Unreachable() << "Not sure how to set different limits for calls to solve in "
                   "ApproxMC";
  return solve();
}

SatValue ApproxMCounter::solve(const std::vector<SatLiteral>& assumptions)
{
  std::cout << "[ApproxMC] called with assumptions" << std::endl;
  std::vector<CMSat::Lit> assumpts;
  for (const SatLiteral& lit : assumptions)
  {
    assumpts.push_back(toInternalLit(lit));
  }
  ++d_statistics.d_statCallsToSolve;
  std::cout << "[ApproxMC] Skipping " << assumpts.size()
            << " assumptions (TODO?)" << std::endl;
  return solve();  // TODO decide what is to be done here.
}

void ApproxMCounter::getUnsatAssumptions(std::vector<SatLiteral>& assumptions)
{
}

SatValue ApproxMCounter::value(SatLiteral l) { return SAT_VALUE_UNKNOWN; }

SatValue ApproxMCounter::modelValue(SatLiteral l) { return value(l); }

unsigned ApproxMCounter::getAssertionLevel() const
{
  Unreachable() << "No interface to get assertion level in Cryptominisat";
  return -1;
}

// Satistics for ApproxMCounter

ApproxMCounter::Statistics::Statistics(StatisticsRegistry& registry,
                                       const std::string& prefix)
    : d_statCallsToSolve(
        registry.registerInt(prefix + "cryptominisat::calls_to_solve")),
      d_xorClausesAdded(
          registry.registerInt(prefix + "cryptominisat::xor_clauses")),
      d_clausesAdded(registry.registerInt(prefix + "cryptominisat::clauses")),
      d_solveTime(registry.registerTimer(prefix + "cryptominisat::solve_time"))
{
}

}  // namespace prop
}  // namespace cvc5::internal
#endif
