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

// #include "cvc5_public.h"

#ifndef CVC5__SMT__HASHGEN_H
#define CVC5__SMT__HASHGEN_H

#include <bits/stdc++.h>

#include <cmath>

#include "api/cpp/cvc5.h"
#include "base/check.h"

/**
 * Function: computeNewBitwidth
 */

int computeNewBitwidth(int k, int slices, std::map<int, int> varMap)
{
  long long totalBitwidth = 0;
  int newBitwidth;

  for (auto item : varMap)
  {
    totalBitwidth += ceil(float(item.second) / k);
  }

  newBitwidth = k + int(ceil(log(slices * totalBitwidth))) + 1;
  // +1 since 's' can be upto 'prime-1'

  return newBitwidth;
}

/**
 * Function ExtractExpr
 * TODO
 */
int zeroExtendExpr(int a, int b) { return 0; }

/**
 * Function zeroExtendExpr
 * TODO
 */
int extractExpr(int msbPos, int lsbPos, int key) { return 0; }

/**
 * Function: generateEquationConstraint
 * @param varmap a map of variables with key as variable name and value being
 *         its width
 * @param maxBitwidth maximum bitwidth
 * @param slices number of slices for each variable to create
 *
 * @return Generates an equation of the form:
 *     a1x1 + a2x2 + ... = s*prime + r
 */

cvc5::Term generateEquationConstraint(std::map<int, int> varMap,
                                      std::map<int, int> primesMap,
                                      int maxBitwidth,
                                      int slices)
{
  static int counter = 0;
  counter += 1;

  int k = int(ceil(float(maxBitwidth) / slices));

  long long twoPowerK = pow(2, k);
  int prime = primesMap[k];

  int newBitwidth = computeNewBitwidth(k, slices, varMap);

  //     primeCoeff = "temp_prime_coeff_" +
  //     str(generateEquationConstraint.counter) primeCoeffDecl = "(declare-fun
  //     " + primeCoeff + " () (_ BitVec " + str(newBitwidth - (k + 1)) + "))\n"

  std::vector<int> bvmulList;

  for (auto item : varMap)
  {
    int key = item.first;
    int originalKey = key;

    if (varMap[key] != maxBitwidth)
      key = zeroExtendExpr(maxBitwidth - varMap[key], key);

    Assert(maxBitwidth >= slices);

    // find slice widths of variable
    int keyDivWidth = int(maxBitwidth / slices);
    int bitRemaining = maxBitwidth % slices;

    // list containing width of each variable slice
    std::vector<int> keyDivWidthList;  // TODO = [keyDivWidth] * slices;

    for (int i = 0; i < bitRemaining; i++)
    {
      keyDivWidthList[i] += 1;
    }

    std::vector<int> coeff;

    for (int i = 0; i < slices; i++)
    {
      coeff.push_back(rand() % twoPowerK);
    }

    std::vector<int> keyDivs;
    int msbPos = maxBitwidth - 1;
    int remSlices = 0;
    for (int i = 0; i < slices; i++)
    {
      int lsbPos = msbPos - keyDivWidthList[i] + 1;
      if (lsbPos < varMap[originalKey])
      {
        keyDivs.push_back(extractExpr(msbPos, lsbPos, key));
        remSlices += 1;
      }
      msbPos = msbPos - keyDivWidthList[i];
    }
    std::vector<int> zxtndKeyDivs;
    for (int i = 0; i < remSlices; i++)
    {
      zxtndKeyDivs.push_back(
          zeroExtendExpr(newBitwidth - keyDivWidthList[i], keyDivs[i]));
    }

    std::vector<int> bvmulStrs;
    for (int i = 0; i < remSlices; i++)
    {
      bvmulList.push_back(
          bvmulExpr(constExpr(coeff[i], newBitwidth), zxtndKeyDivs[i]));
    }
  }

  /* TODO this part is crazy difficuilt

  lhsStr = functools.reduce(lambda x, y : bvaddExpr(x, y), bvmulList);

  s = zeroExtendExpr(k + 1, primeCoeff);
  r = random.randint(0, prime - 1);

  rhsStr = bvaddExpr(bvmulExpr(constExpr(prime, newBitwidth), s),
                     constExpr(r, newBitwidth));
  constraint = eqExpr(lhsStr, rhsStr);
  return constraint, primeCoeffDecl, prime
 */
}
#endif /* CVC5__SMT__HASHGEN_H */
