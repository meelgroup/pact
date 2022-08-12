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

#include "cvc5_private.h"

#ifndef CVC5__PROP__APPROXMC_H
#define CVC5__PROP__APPROXMC_H

#include "prop/sat_solver.h"

namespace ApproxMC {
class AppMC;
}

namespace cvc5::internal {
namespace prop {

class ApproxMCounter : public SatSolver
{
  friend class SatSolverFactory;

 public:
  ~ApproxMCounter() override;

  ClauseId addClause(SatClause& clause, bool removable) override;

  ClauseId addXorClause(SatClause& clause, bool rhs, bool removable) override;

  SatVariable newVar(bool isTheoryAtom = false,
                     bool preRegister = false,
                     bool canErase = true) override;

  SatVariable trueVar() override;

  SatVariable falseVar() override;

  SatValue solve() override;
  SatValue solve(long unsigned int&) override;
  SatValue solve(const std::vector<SatLiteral>& assumptions) override;
  void getUnsatAssumptions(std::vector<SatLiteral>& assumptions) override;

  void interrupt() override;

  SatValue value(SatLiteral l) override;

  SatValue modelValue(SatLiteral l) override;

  unsigned getAssertionLevel() const override;

  bool ok() const override;

 private:
  /**
   * Private to disallow creation outside of SatSolverFactory.
   * Function init() must be called after creation.
   */
  ApproxMCounter(StatisticsRegistry& registry, const std::string& name = "");
  /**
   * Initialize SAT solver instance.
   * Note: Split out to not call virtual functions in constructor.
   */
  void init();

  /**
   * Set resource limit.
   */
  void setResourceLimit(ResourceManager* resmgr);

  std::unique_ptr<ApproxMC::AppMC> d_counter;

  /**
   * Stores the current set of assumptions provided via solve() and is used to
   * query the solver if a given assumption is false.
   */
  std::vector<SatLiteral> d_assumptions;

  unsigned d_nextVarIdx;
  bool d_inSatMode;
  SatVariable d_true;
  SatVariable d_false;

  class Statistics
  {
   public:
    IntStat d_statCallsToSolve;
    IntStat d_xorClausesAdded;
    IntStat d_clausesAdded;
    TimerStat d_solveTime;
    Statistics(StatisticsRegistry& registry, const std::string& prefix);
  };

  unsigned d_numVariables;
  bool d_okay;
  Statistics d_statistics;
  ResourceManager* d_resmgr;
};

}  // namespace prop
}  // namespace cvc5::internal

#endif  // CVC5__PROP__APPROXMC_H
