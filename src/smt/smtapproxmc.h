/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * SMTApproxMC : Implementation of Approximate Model Counter with
 * word level hash functions
 */

#include "cvc5_public.h"

#ifndef CVC5__SMTAPPROXMC_H
#define CVC5__SMTAPPROXMC_H

#include "cvc5_export.h"
#include "options/options.h"

namespace cvc5 {

namespace internal {

class CVC5_EXPORT SMTApproxMC
{
  double epsilon;
  double numiteration;
  uint64_t minPivot, maxPivot;

 public:
  SMTApproxMC(const Options* optr = nullptr);
  ~SMTApproxMC();

  uint64_t smtApxInnerLoop();
  uint64_t smtApxOuterLoop();
};

}  // namespace internal
}  // namespace cvc5

#endif  // CVC5__SMTAPPROXMC_H
