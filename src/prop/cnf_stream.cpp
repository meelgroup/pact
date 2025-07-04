/******************************************************************************
 * Top contributors (to current version):
 *   Dejan Jovanovic, Haniel Barbosa, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A CNF converter that takes in asserts and has the side effect of given an
 * equisatisfiable stream of assertions to PropEngine.
 */
#include "prop/cnf_stream.h"

#include <queue>

#include "base/check.h"
#include "base/output.h"
#include "expr/node.h"
#include "options/base_options.h"
#include "options/bv_options.h"
#include "options/main_options.h"
#include "options/counting_options.h"
#include "printer/printer.h"
#include "proof/clause_id.h"
#include "prop/minisat/minisat.h"
#include "prop/prop_engine.h"
#include "prop/theory_proxy.h"
#include "smt/env.h"
#include "theory/theory.h"
#include "theory/theory_engine.h"

namespace cvc5::internal {
namespace prop {

CnfStream::CnfStream(Env& env,
                     SatSolver* satSolver,
                     Registrar* registrar,
                     context::Context* c,
                     FormulaLitPolicy flpol,
                     std::string name)
    : EnvObj(env),
      d_satSolver(satSolver),
      d_booleanVariables(c),
      d_notifyFormulas(c),
      d_nodeToLiteralMap(c),
      d_literalToNodeMap(c),
      d_flitPolicy(flpol),
      d_registrar(registrar),
      d_name(name),
      d_removable(false),
      d_stats(statisticsRegistry(), name)
{
}

bool CnfStream::assertClause(TNode node, SatClause& c)
{
  Trace("cnf") << "Inserting into stream " << c << " node = " << node << "\n";

  ClauseId clauseId = d_satSolver->addClause(c, d_removable);

  return clauseId != ClauseIdUndef;
}

bool CnfStream::assertClause(TNode node, SatLiteral a)
{
  SatClause clause(1);
  clause[0] = a;
  return assertClause(node, clause);
}

bool CnfStream::assertClause(TNode node, SatLiteral a, SatLiteral b)
{
  SatClause clause(2);
  clause[0] = a;
  clause[1] = b;
  return assertClause(node, clause);
}

bool CnfStream::assertXorClause(TNode node, SatClause& c)
{
  Trace("cnf-xor") << "Inserting XOR into stream " << c << " node = " << node
                   << "\n";

  ClauseId clauseId = d_satSolver->addXorClause(c, 0, d_removable);

  return clauseId != ClauseIdUndef;
}

bool CnfStream::assertXorClause(TNode node, SatLiteral a, SatLiteral b)
{
  SatClause clause(2);
  clause[0] = a;
  clause[1] = b;
  return assertXorClause(node, clause);
}

bool CnfStream::assertXorClause(TNode node,
                                SatLiteral a,
                                SatLiteral b,
                                SatLiteral c)
{
  SatClause clause(3);
  clause[0] = a;
  clause[1] = b;
  clause[2] = c;
  return assertXorClause(node, clause);
}

bool CnfStream::assertClause(TNode node,
                             SatLiteral a,
                             SatLiteral b,
                             SatLiteral c)
{
  SatClause clause(3);
  clause[0] = a;
  clause[1] = b;
  clause[2] = c;
  return assertClause(node, clause);
}

bool CnfStream::hasLiteral(TNode n) const
{
  NodeToLiteralMap::const_iterator find = d_nodeToLiteralMap.find(n);
  return find != d_nodeToLiteralMap.end();
}

void CnfStream::ensureMappingForLiteral(TNode n)
{
  SatLiteral lit = getLiteral(n);
  if (!d_literalToNodeMap.contains(lit))
  {
    // Store backward-mappings
    d_literalToNodeMap.insert(lit, n);
    d_literalToNodeMap.insert(~lit, n.notNode());
  }
}

void CnfStream::ensureLiteral(TNode n)
{
  AlwaysAssertArgument(
      hasLiteral(n) || n.getType().isBoolean(),
      n,
      "ProofCnfStream::ensureLiteral() requires a node of Boolean type.\n"
      "got node: %s\n"
      "its type: %s\n",
      n.toString().c_str(),
      n.getType().toString().c_str());
  Trace("cnf") << "ensureLiteral(" << n << ")\n";
  TimerStat::CodeTimer codeTimer(d_stats.d_cnfConversionTime, true);
  if (hasLiteral(n))
  {
    ensureMappingForLiteral(n);
    return;
  }
  // remove top level negation
  n = n.getKind() == Kind::NOT ? n[0] : n;
  if (d_env.theoryOf(n) == theory::THEORY_BOOL && !n.isVar())
  {
    // If we were called with something other than a theory atom (or
    // Boolean variable), we get a SatLiteral that is definitionally
    // equal to it.
    // These are not removable and have no proof ID
    d_removable = false;

    SatLiteral lit = toCNF(n, false);

    // Store backward-mappings
    // These may already exist
    d_literalToNodeMap.insert_safe(lit, n);
    d_literalToNodeMap.insert_safe(~lit, n.notNode());
  }
  else
  {
    // We have a theory atom or variable.
    convertAtom(n);
  }
}

SatLiteral CnfStream::newLiteral(TNode node,
                                 bool isTheoryAtom,
                                 bool notifyTheory,
                                 bool canEliminate)
{
  Trace("cnf") << d_name << "::newLiteral(" << node << ", " << isTheoryAtom
               << ")\n"
               << push;
  Assert(node.getKind() != Kind::NOT);

  // if we are tracking formulas, everything is a theory atom
  if (!isTheoryAtom && d_flitPolicy == FormulaLitPolicy::TRACK_AND_NOTIFY)
  {
    isTheoryAtom = true;
    d_notifyFormulas.insert(node);
  }

  // Get the literal for this node
  SatLiteral lit;
  if (!hasLiteral(node))
  {
    Trace("cnf") << d_name << "::newLiteral: node already registered\n";
    // If no literal, we'll make one
    if (node.getKind() == Kind::CONST_BOOLEAN)
    {
      Trace("cnf") << d_name << "::newLiteral: boolean const\n";
      if (node.getConst<bool>())
      {
        lit = SatLiteral(d_satSolver->trueVar());
      }
      else
      {
        lit = SatLiteral(d_satSolver->falseVar());
      }
    }
    else
    {
      Trace("cnf") << d_name << "::newLiteral: new var\n";
      lit = SatLiteral(d_satSolver->newVar(isTheoryAtom, canEliminate));
      d_stats.d_numAtoms++;
    }
    d_nodeToLiteralMap.insert(node, lit);
    d_nodeToLiteralMap.insert(node.notNode(), ~lit);
  }
  else
  {
    Trace("cnf") << d_name << "::newLiteral: node already registered\n";
    lit = getLiteral(node);
  }

  // If it's a theory literal, need to store it for back queries
  if (isTheoryAtom || d_flitPolicy == FormulaLitPolicy::TRACK
      || d_flitPolicy == FormulaLitPolicy::TRACK_AND_NOTIFY_VAR)
  {
    d_literalToNodeMap.insert_safe(lit, node);
    d_literalToNodeMap.insert_safe(~lit, node.notNode());
  }

  // If a theory literal, we pre-register it
  if (notifyTheory)
  {
    // In case we are re-entered due to lemmas, save our state
    bool backupRemovable = d_removable;
    d_registrar->notifySatLiteral(node);
    d_removable = backupRemovable;
  }
  // Here, you can have it
  Trace("cnf") << "newLiteral(" << node << ") => " << lit << "\n" << pop;
  return lit;
}

TNode CnfStream::getNode(const SatLiteral& literal)
{
  Assert(d_literalToNodeMap.find(literal) != d_literalToNodeMap.end());
  Trace("cnf") << "getNode(" << literal << ")\n";
  Trace("cnf") << "getNode(" << literal << ") => "
               << d_literalToNodeMap[literal] << "\n";
  return d_literalToNodeMap[literal];
}

const CnfStream::NodeToLiteralMap& CnfStream::getTranslationCache() const
{
  return d_nodeToLiteralMap;
}

const CnfStream::LiteralToNodeMap& CnfStream::getNodeCache() const
{
  return d_literalToNodeMap;
}

void CnfStream::getBooleanVariables(std::vector<TNode>& outputVariables) const
{
  outputVariables.insert(outputVariables.end(),
                         d_booleanVariables.begin(),
                         d_booleanVariables.end());
}

bool CnfStream::isNotifyFormula(TNode node) const
{
  return d_notifyFormulas.find(node) != d_notifyFormulas.end();
}

SatLiteral CnfStream::convertAtom(TNode node)
{
  Trace("cnf") << "convertAtom(" << node << ")\n";

  Assert(!hasLiteral(node)) << "atom already mapped!";

  bool theoryLiteral = false;
  bool canEliminate = true;
  bool preRegister = false;

  // Is this a variable add it to the list. We distinguish whether a Boolean
  // variable has been marked as a "Boolean term skolem". These variables are
  // introduced by the term formula removal pass (term_formula_removal.h)
  // and maintained by Env (smt/env.h). We treat such variables as theory atoms
  // since they may occur in term positions and thus need to be considered e.g.
  // for theory combination.
  bool isInternalBoolVar = false;
  if (node.isVar())
  {
    isInternalBoolVar = !d_env.isBooleanTermSkolem(node);
  }
  if (isInternalBoolVar)
  {
    d_booleanVariables.push_back(node);
    // if TRACK_AND_NOTIFY_VAR, we are notified when Boolean variables are
    // asserted. Thus, they are marked as theory literals.
    if (d_flitPolicy == FormulaLitPolicy::TRACK_AND_NOTIFY_VAR)
    {
      theoryLiteral = true;
    }
  }
  else
  {
    theoryLiteral = true;
    canEliminate = false;
    preRegister = true;
  }

  // Make a new literal (variables are not considered theory literals)
  SatLiteral lit = newLiteral(node, theoryLiteral, preRegister, canEliminate);
  // Return the resulting literal
  return lit;
}

SatLiteral CnfStream::getLiteral(TNode node) {
  Assert(!node.isNull()) << "CnfStream: can't getLiteral() of null node";

  Assert(d_nodeToLiteralMap.contains(node))
      << "Literal not in the CNF Cache: " << node << "\n";

  SatLiteral literal = d_nodeToLiteralMap[node];
  Trace("cnf") << "CnfStream::getLiteral(" << node << ") => " << literal
               << "\n";
  if (options().base.boolabs)
  {
    auto printnode = node;
    auto printliteral = literal;
    if (node.getKind() == Kind::NOT)
    {
      printnode = node.negate();
      printliteral = ~literal;
    }
    if (printnode.getKind() == Kind::EQUAL || printnode.getKind() == Kind::GEQ)
    {
      Trace("aiginfo") << "c " << printliteral << ":" << printnode << std::endl;
    }
    else
    {
      Trace("aiginfo") << "c " << printliteral << ": skipit" << std::endl;
    }
  }
  return literal;
}

int64_t CnfStream::negateAIGVar(int64_t aigVar)
{
  bool negative = (aigVar < 0);
  aigVar = std::abs(aigVar);
  if (aigVar % 2 == 1)
  {
    aigVar -= 1;
  }
  else
  {
    aigVar += 1;
  }
  if (negative)
  {
    aigVar = -aigVar;
  }
  return aigVar;
}

int64_t CnfStream::newAIGVar(bool negated)
{
  (--maxAIGrootvar);
  return 2 * maxAIGrootvar - (negated ? 1 : 0);
}

int64_t CnfStream::getAIGliteral(SatLiteral lit, Node node, bool isOutput, bool donegate )
{
  // TODO some checks like the first literal can't be or and
  // should be good to have


  bool wasNegated = false;
  SatVariable satVar = lit.getSatVariable();
  SatVariable aigVar = satVar * 2;
  if (satVar > maxAIGVar)
  {
    maxAIGVar = satVar;
  }
  Trace("aig-debug") << "getAIGliteral(" << lit << ", " << node << ", "
                     << isOutput << ", " << donegate << ") => ";

  if (node.getKind() == Kind::NOT)
  {
    node = node[0];
    wasNegated = true;
  }

  auto nodeKind = node.getKind();

  if (nodeKind == Kind::EQUAL || nodeKind == Kind::GEQ || nodeKind == Kind::VARIABLE)
  {
    aigInputLits.push_back(aigVar);
  }
  if (lit.isNegated())
  {
    donegate = !donegate;
  }
  // if (wasNegated)
  // {
  //   donegate = !donegate;
  // }
  if (donegate){
    aigVar = negateAIGVar(aigVar);
  }
  if (isOutput && aigVar % 2 == 1)
  {
    aigVar -= 1;
  }
  Trace("aig-debug") << aigVar << std::endl;
  if ((nodeKind == Kind::EQUAL || nodeKind == Kind::GEQ || nodeKind == Kind::VARIABLE))
  {
    Trace("boolabs") << "c " << aigVar << ":" << node << std::endl;
  }
  Trace("aig-allvar") << "c " << aigVar << ":" << node << std::endl;
  return aigVar;
}

// this is assumed to be called from dumpAIG, which is supposed to be called
// after all the clauses have been asserted from propEngine
vector<vector<int64_t>> CnfStream::decomposeAndGate(vector<int64_t> andGate)
{
  Trace("aiginfo") << "Decomposing AND gate" << std::endl;
  Trace("aig-debug") << "AND gate: ";
  {
    int64_t first = andGate[0];
    std::vector<int64_t> uniqueAndGate;
    uniqueAndGate.push_back(first);
    std::unordered_set<int64_t> seen{first};
    for (size_t i = 1; i < andGate.size(); ++i)
    {
      if (seen.insert(andGate[i]).second)
      {
        uniqueAndGate.push_back(andGate[i]);
      }
    }
    andGate = uniqueAndGate;
  }
  for (auto aiglit : andGate)
  {
    Trace("aig-debug") << aiglit << " ";
  }
  Trace("aig-debug") << std::endl;
  vector<vector<int64_t>> decomposedGates;
  if (andGate.size() <= 2)
  {
    decomposedGates.push_back(andGate);
    return decomposedGates;
  }

  int64_t outputLit = andGate[0];
  for (size_t i = 1; i < andGate.size() - 1; ++i)
  {
    int64_t nextLiteral =
        (i == andGate.size() - 2) ? andGate[i + 1] : (maxAIGVar += 1) * 2;
    decomposedGates.push_back({outputLit, andGate[i], nextLiteral});
    outputLit = nextLiteral;
  }
  std::reverse(decomposedGates.begin(), decomposedGates.end());
  Trace("aig-debug") << "Decomposed AND gate" << std::endl;
  for (auto decomposedGate : decomposedGates)
  {
    for (auto aiglit : decomposedGate)
    {
      Trace("aig-debug") << aiglit << " ";
    }
    Trace("aig-debug") << std::endl;
  }
  return decomposedGates;
}

void CnfStream::printAigGateLines(std::string name)
{
  Trace("aig-debug") << "Printing entire AIG gate lines from " << name
                   << std::endl;
  for (const auto& gateLine : aigGateLines)
  {
    for (const auto& lit : gateLine)
    {
      Trace("aig-debug") << lit << " ";
    }
    Trace("aig-debug") << std::endl;
  }
}

void CnfStream::dumpAIG()
{
  // File creation

  std::string smtfilename = options().driver.filename;
  std::string aigfilename =
      smtfilename.substr(smtfilename.find_last_of("/\\") + 1);
  aigfilename = aigfilename.substr(0, aigfilename.find_last_of(".")) + ".aag";
  Trace("aiginfo") << "Writing AIG to " << aigfilename << std::endl;
  std::ofstream outFile(aigfilename);
  if (!outFile)
  {
    std::cerr << "Error creating file: " << aigfilename << std::endl;
    return;
  }

  // Increasing maxAIGVar to accomodate assert lits
  // auxiliar variables -- first the assert lits, then the real aux

  Trace("aiginfo") << "increasing maxAIGVar by " << -maxAIGrootvar << " from "
                   << maxAIGVar << " to " << maxAIGVar - maxAIGrootvar
                   << std::endl;

  int64_t incrementForRootVar = maxAIGVar * 2;

  maxAIGVar -= maxAIGrootvar;

  // Fixing the output literal
  aigOutputLit = 2;
  std::vector<int64_t> outputLitLine = {2};

  for (auto& lit : aigAssertLits)
  {
    if (lit < 0)
    {
      Trace("aig-debug") << "c asserting literal " << lit << " to "
                       << -lit + incrementForRootVar << std::endl;
      lit = -lit + incrementForRootVar;
    }
  }

  aigAssertLits.erase(
    std::remove(aigAssertLits.begin(), aigAssertLits.end(), 2),
    aigAssertLits.end());

  if (aigAssertLits.size() == 1)
  {
    outputLitLine = aigAssertLits;
    aigOutputLit = aigAssertLits[0];
    Trace("aig-debug") << "c single literal output:" << outputLitLine[0] << std::endl;
  }
  else {

    for (auto aigAssertLit : aigAssertLits)
    {
      if (aigAssertLit <= 5)
      {
        continue;
      }
      outputLitLine.push_back(aigAssertLit);
    }
    aigGateLines.push_back(outputLitLine);
}

  vector<vector<int64_t>> decomposedGates;
  for (auto aigline : aigGateLines)
  {
    auto thisGateDecomposed = decomposeAndGate(aigline);
    for (auto gate : thisGateDecomposed)
    {
      decomposedGates.push_back(gate);
    }
  }



  std::unordered_set<int64_t> uniqueInputs(aigInputLits.begin(), aigInputLits.end());
  aigInputLits.assign(uniqueInputs.begin(), uniqueInputs.end());

  // set and print the header
  outFile << "aag " << maxAIGVar << " " << aigInputLits.size() << " 0 1 "
          << decomposedGates.size() << std::endl;

  // print the input literals
  for (auto aigInputLit : aigInputLits)
  {
    outFile << aigInputLit << std::endl;
  }

  // print the output literals
  outFile << aigOutputLit << std::endl;

  for (auto aigdecomposedline : decomposedGates)
  {
    std::string aigstring;
    for (auto aiglit : aigdecomposedline)
    {
      if(aiglit < 0){
        Trace("aig-debug") << "c negative literal" << aiglit
        << " incremented to " << -aiglit + incrementForRootVar << std::endl;
        aiglit = -aiglit + incrementForRootVar;
        if (aiglit %2 == 1) {
          aiglit = aiglit - 1;
        }
      }
      aigstring += " " + std::to_string(aiglit);
    }
    aigstring = aigstring.substr(1);
    outFile << aigstring << std::endl;
  }
  Trace("aig-debug") << "c end AIG output\n";
  Trace("aiginfo")
      << "exit -------------------------------------- [AIG Dump Done]"
      << std::endl;
}

void CnfStream::handleXor(TNode xorNode)
{
  Assert(!hasLiteral(xorNode)) << "Atom already mapped!";
  Assert(xorNode.getKind() == Kind::XOR) << "Expecting an XOR expression!";
  Assert(xorNode.getNumChildren() == 2) << "Expecting exactly 2 children!";
  Assert(!d_removable) << "Removable clauses can not contain Boolean structure";
  Trace("cnf-xor") << "CnfStream::handleXor(" << xorNode << ")\n";

  if (!options().counting.projcount)
  {
    SatLiteral xorLit = newLiteral(xorNode);
    SatLiteral a = getLiteral(xorNode[0]);
    SatLiteral b = getLiteral(xorNode[1]);
    // xorLit = true as addXorClause(c, *0*, d_removable);
    assertXorClause(xorNode, a, b, xorLit);
  }
  else if (false)
  {

    size_t numChildren = xorNode.getNumChildren();

    // Get the literal for this node
    SatLiteral xorLit = newLiteral(xorNode);

    // Transform all the children first
    SatClause clause(numChildren + 1);
    for (size_t i = 0; i < numChildren; ++i)
    {
      clause[i] = getLiteral(xorNode[i]);

      // lit <- (a_1 x a_2 x a_3 x ... x a_n)
      // lit | ~(a_1 | a_2 | a_3 | ... | a_n)
      // (lit | ~a_1) & (lit | ~a_2) & (lit & ~a_3) & ... & (lit & ~a_n)
      assertClause(xorNode, xorLit, ~clause[i]);
    }

    // lit -> (a_1 | a_2 | a_3 | ... | a_n)
    // ~lit | a_1 | a_2 | a_3 | ... | a_n
    clause[numChildren] = ~xorLit;
    // This needs to go last, as the clause might get modified by the SAT solver
    assertClause(xorNode.negate(), clause);
  }
  else
  {
    Trace("cnf-xor") << "CnfStream::handleXor: using xor encoding\n";
    SatLiteral a = getLiteral(xorNode[0]);
    SatLiteral b = getLiteral(xorNode[1]);

    SatLiteral xorLit = newLiteral(xorNode);
    assertClause(xorNode.negate(), a, b, ~xorLit);
    assertClause(xorNode.negate(), ~a, ~b, ~xorLit);
    assertClause(xorNode, a, ~b, xorLit);
    assertClause(xorNode, ~a, b, xorLit);
  }
}

void CnfStream::handleOr(TNode orNode)
{
  Assert(!hasLiteral(orNode)) << "Atom already mapped!";
  Assert(orNode.getKind() == Kind::OR) << "Expecting an OR expression!";
  Assert(orNode.getNumChildren() > 1) << "Expecting more then 1 child!";
  Assert(!d_removable) << "Removable clauses can not contain Boolean structure";
  Trace("cnf") << "CnfStream::handleOr(" << orNode << ")\n";

  // Number of children
  size_t numChildren = orNode.getNumChildren();

  // Get the literal for this node
  SatLiteral orLit = newLiteral(orNode);
  std::vector<int64_t> aigliterals;

  // orLit are not added as negation, as the gate output can't be negated
  // it is asserted during getAIGliteral that if a orLit is found
  // handle that after negating the literal
  aigliterals.push_back(getAIGliteral(orLit, orNode, false, true));
  Trace("aig-debug") << "sending or clause:"
                     << getAIGliteral(orLit, orNode, false, true) << std::endl;
  // Transform all the children first
  SatClause clause(numChildren + 1);
  for (size_t i = 0; i < numChildren; ++i)
  {
    clause[i] = getLiteral(orNode[i]);

    // lit <- (a_1 | a_2 | a_3 | ... | a_n)
    // lit | ~(a_1 | a_2 | a_3 | ... | a_n)
    // (lit | ~a_1) & (lit | ~a_2) & (lit & ~a_3) & ... & (lit & ~a_n)
    assertClause(orNode, orLit, ~clause[i]);
    Trace("aig-debug") << "sending or clause" << std::endl;
    aigliterals.push_back(getAIGliteral(~clause[i], orNode[i]));
  }

  // lit -> (a_1 | a_2 | a_3 | ... | a_n)
  // ~lit | a_1 | a_2 | a_3 | ... | a_n
  clause[numChildren] = ~orLit;
  // This needs to go last, as the clause might get modified by the SAT solver
  assertClause(orNode.negate(), clause);
  aigGateLines.push_back(aigliterals);
  printAigGateLines("handleOr");
}

void CnfStream::handleAnd(TNode andNode)
{
  Assert(!hasLiteral(andNode)) << "Atom already mapped!";
  Assert(andNode.getKind() == Kind::AND) << "Expecting an AND expression!";
  Assert(andNode.getNumChildren() > 1) << "Expecting more than 1 child!";
  Assert(!d_removable) << "Removable clauses can not contain Boolean structure";
  Trace("cnf") << "handleAnd(" << andNode << ")\n";

  // Number of children
  size_t numChildren = andNode.getNumChildren();

  // Get the literal for this node
  SatLiteral andLit = newLiteral(andNode);

  std::vector<int64_t> aigliterals;
  aigliterals.push_back(getAIGliteral(andLit, andNode, true, false));
  Trace("aig-debug") << "sending and clause: "
                         << getAIGliteral(andLit, andNode) << std::endl;

  // Transform all the children first (remembering the negation)
  SatClause clause(numChildren + 1);
  for (size_t i = 0; i < numChildren; ++i)
  {
    clause[i] = ~getLiteral(andNode[i]);

    // lit -> (a_1 & a_2 & a_3 & ... & a_n)
    // ~lit | (a_1 & a_2 & a_3 & ... & a_n)
    // (~lit | a_1) & (~lit | a_2) & ... & (~lit | a_n)
    assertClause(andNode.negate(), ~andLit, ~clause[i]);
    aigliterals.push_back(getAIGliteral(~clause[i], andNode[i]));
  }

  aigGateLines.push_back(aigliterals);
  printAigGateLines("handleAnd");

  // lit <- (a_1 & a_2 & a_3 & ... a_n)
  // lit | ~(a_1 & a_2 & a_3 & ... & a_n)
  // lit | ~a_1 | ~a_2 | ~a_3 | ... | ~a_n
  clause[numChildren] = andLit;
  // This needs to go last, as the clause might get modified by the SAT solver
  assertClause(andNode, clause);
}

void CnfStream::handleImplies(TNode impliesNode)
{
  Assert(!hasLiteral(impliesNode)) << "Atom already mapped!";
  Assert(impliesNode.getKind() == Kind::IMPLIES)
      << "Expecting an IMPLIES expression!";
  Assert(impliesNode.getNumChildren() == 2) << "Expecting exactly 2 children!";
  Assert(!d_removable) << "Removable clauses can not contain Boolean structure";
  Trace("cnf") << "handleImplies(" << impliesNode << ")\n";

  // Convert the children to cnf
  SatLiteral a = getLiteral(impliesNode[0]);
  SatLiteral b = getLiteral(impliesNode[1]);

  SatLiteral impliesLit = newLiteral(impliesNode);

  // lit -> (a->b)
  // ~lit | ~ a | b
  assertClause(impliesNode.negate(), ~impliesLit, ~a, b);

  // (a->b) -> lit
  // ~(~a | b) | lit
  // (a | l) & (~b | l)
  assertClause(impliesNode, a, impliesLit);
  assertClause(impliesNode, ~b, impliesLit);
}

void CnfStream::handleIff(TNode iffNode)
{
  Assert(!hasLiteral(iffNode)) << "Atom already mapped!";
  Assert(iffNode.getKind() == Kind::EQUAL) << "Expecting an EQUAL expression!";
  Assert(iffNode.getNumChildren() == 2) << "Expecting exactly 2 children!";
  Assert(!d_removable) << "Removable clauses can not contain Boolean structure";
  Trace("cnf") << "handleIff(" << iffNode << ")\n";

  // Convert the children to CNF
  SatLiteral a = getLiteral(iffNode[0]);
  SatLiteral b = getLiteral(iffNode[1]);

  // Get the now literal
  SatLiteral iffLit = newLiteral(iffNode);

  // lit -> ((a-> b) & (b->a))
  // ~lit | ((~a | b) & (~b | a))
  // (~a | b | ~lit) & (~b | a | ~lit)
  assertClause(iffNode.negate(), ~a, b, ~iffLit);
  assertClause(iffNode.negate(), a, ~b, ~iffLit);

  // (a<->b) -> lit
  // ~((a & b) | (~a & ~b)) | lit
  // (~(a & b)) & (~(~a & ~b)) | lit
  // ((~a | ~b) & (a | b)) | lit
  // (~a | ~b | lit) & (a | b | lit)
  assertClause(iffNode, ~a, ~b, iffLit);
  assertClause(iffNode, a, b, iffLit);
}

void CnfStream::handleIte(TNode iteNode)
{
  Assert(!hasLiteral(iteNode)) << "Atom already mapped!";
  Assert(iteNode.getKind() == Kind::ITE);
  Assert(iteNode.getNumChildren() == 3);
  Assert(!d_removable) << "Removable clauses can not contain Boolean structure";
  Trace("cnf") << "handleIte(" << iteNode[0] << " " << iteNode[1] << " "
               << iteNode[2] << ")\n";

  SatLiteral condLit = getLiteral(iteNode[0]);
  SatLiteral thenLit = getLiteral(iteNode[1]);
  SatLiteral elseLit = getLiteral(iteNode[2]);

  SatLiteral iteLit = newLiteral(iteNode);

  // If ITE is true then one of the branches is true and the condition
  // implies which one
  // lit -> (ite b t e)
  // lit -> (t | e) & (b -> t) & (!b -> e)
  // lit -> (t | e) & (!b | t) & (b | e)
  // (!lit | t | e) & (!lit | !b | t) & (!lit | b | e)
  assertClause(iteNode.negate(), ~iteLit, thenLit, elseLit);
  assertClause(iteNode.negate(), ~iteLit, ~condLit, thenLit);
  assertClause(iteNode.negate(), ~iteLit, condLit, elseLit);

  // If ITE is false then one of the branches is false and the condition
  // implies which one
  // !lit -> !(ite b t e)
  // !lit -> (!t | !e) & (b -> !t) & (!b -> !e)
  // !lit -> (!t | !e) & (!b | !t) & (b | !e)
  // (lit | !t | !e) & (lit | !b | !t) & (lit | b | !e)
  assertClause(iteNode, iteLit, ~thenLit, ~elseLit);
  assertClause(iteNode, iteLit, ~condLit, ~thenLit);
  assertClause(iteNode, iteLit, condLit, ~elseLit);
}

SatLiteral CnfStream::toCNF(TNode node, bool negated)
{
  Trace("cnf") << "toCNF(" << node
               << ", negated = " << (negated ? "true" : "false") << ")\n";

  TNode cur;
  SatLiteral nodeLit;
  std::vector<TNode> visit;
  std::unordered_map<TNode, bool> cache;

  visit.push_back(node);
  while (!visit.empty())
  {
    cur = visit.back();
    Assert(cur.getType().isBoolean());

    if (hasLiteral(cur))
    {
      visit.pop_back();
      continue;
    }

    const auto& it = cache.find(cur);
    if (it == cache.end())
    {
      cache.emplace(cur, false);
      Kind k = cur.getKind();
      // Only traverse Boolean nodes
      if (k == Kind::NOT || k == Kind::XOR || k == Kind::ITE
          || k == Kind::IMPLIES || k == Kind::OR || k == Kind::AND
          || (k == Kind::EQUAL && cur[0].getType().isBoolean()))
      {
        // Preserve the order of the recursive version
        for (size_t i = 0, size = cur.getNumChildren(); i < size; ++i)
        {
          visit.push_back(cur[size - 1 - i]);
        }
      }
      continue;
    }
    else if (!it->second)
    {
      it->second = true;
      Kind k = cur.getKind();
      switch (k)
      {
        case Kind::NOT: Assert(hasLiteral(cur[0])); break;
        case Kind::XOR: handleXor(cur); break;
        case Kind::ITE: handleIte(cur); break;
        case Kind::IMPLIES: handleImplies(cur); break;
        case Kind::OR: handleOr(cur); break;
        case Kind::AND: handleAnd(cur); break;
        default:
          if (k == Kind::EQUAL && cur[0].getType().isBoolean())
          {
            handleIff(cur);
          }
          else
          {
            convertAtom(cur);
          }
          break;
      }
    }
    visit.pop_back();
  }

  nodeLit = getLiteral(node);

  int64_t aigAssertLit = getAIGliteral(nodeLit, node);
  Trace("aiginfo") << "toAIG(): skipped asserting " << aigAssertLit << std::endl;
  // aigAssertLits.push_back(aigAssertLit);

  Trace("cnf") << "toCNF(): resulting literal: "
               << (!negated ? nodeLit : ~nodeLit) << "\n";
  return negated ? ~nodeLit : nodeLit;
}

void CnfStream::convertAndAssertAnd(TNode node, bool negated, bool root)
{
  Assert(node.getKind() == Kind::AND);
  Trace("cnf") << "CnfStream::convertAndAssertAnd(" << node
               << ", negated = " << (negated ? "true" : "false")
               << ", root = " << (root ? "true" : "false") << ")\n"
               << ")\n";
  std::vector<int64_t> aigliterals;
  int64_t aigOutputVar;
  if (!negated)
  {
    // If the node is a conjunction, we handle each conjunct separately
    for (TNode::const_iterator conjunct = node.begin(), node_end = node.end();
         conjunct != node_end;
         ++conjunct)
    {
      convertAndAssert(*conjunct, false, root);
    }
  }
  else
  {
    aigOutputVar = newAIGVar(false);

    Trace("aiginfo") << "AND gate " << std::endl;

    // If the node is a disjunction, we construct a clause and assert it
    int nChildren = node.getNumChildren();
    SatClause clause(nChildren);
    TNode::const_iterator disjunct = node.begin();
    aigliterals.push_back(aigOutputVar);

    for (int i = 0; i < nChildren; ++disjunct, ++i)
    {
      Assert(disjunct != node.end());
      clause[i] = toCNF(*disjunct, true);
      aigliterals.push_back(getAIGliteral(clause[i], node));
      Trace("aiginfo") << getAIGliteral(clause[i], node) << " ";
    }
    Assert(disjunct == node.end());
    assertClause(node.negate(), clause);
    if (root)
    {
      Trace("aiginfo") << "AND gate root " << aigOutputVar << std::endl;
      aigAssertLits.push_back(aigOutputVar);
    }
    aigGateLines.push_back(aigliterals);
    printAigGateLines("convertAndAssertAnd");
  }

}

void CnfStream::convertAndAssertOr(TNode node, bool negated, bool root)
{
  Assert(node.getKind() == Kind::OR);
  Trace("cnf") << "CnfStream::convertAndAssertOr(" << node
               << ", negated = " << (negated ? "true" : "false")
                << ", root = " << (root ? "true" : "false") << ")\n";
  std::vector<int64_t> aigliterals;
  int64_t aigOutputVar;
  if (!negated)
  {
    // If the node is a disjunction, we construct a clause and assert it
    int nChildren = node.getNumChildren();
    SatClause clause(nChildren);
    TNode::const_iterator disjunct = node.begin();
    aigOutputVar = newAIGVar(true);
    aigliterals.push_back(aigOutputVar);
    for (int i = 0; i < nChildren; ++disjunct, ++i)
    {
      Assert(disjunct != node.end());
      clause[i] = toCNF(*disjunct, false);
      aigliterals.push_back(getAIGliteral(~clause[i], node));
    }
    Assert(disjunct == node.end());
    assertClause(node, clause);
    if (root)
    {
      Trace("aiginfo") << "OR gate root " << aigOutputVar << std::endl;
      aigAssertLits.push_back(aigOutputVar);
    }
    aigGateLines.push_back(aigliterals);
    printAigGateLines("convertAndAssertOr");
  }
  else
  {
    // If the node is a conjunction, we handle each conjunct separately
    for (TNode::const_iterator conjunct = node.begin(), node_end = node.end();
         conjunct != node_end;
         ++conjunct)
    {
      convertAndAssert(*conjunct, true, root);
    }
  }

}

void CnfStream::convertAndAssertXor(TNode node, bool negated, bool root)
{
  Assert(node.getKind() == Kind::XOR);
  Trace("cnf-xor") << "CnfStream::convertAndAssertXor(" << node
                   << ", negated = " << (negated ? "true" : "false")
                   << ", root = " << (root ? "true" : "false") << ")\n";
  if (!negated)
  {
    // p XOR q
    SatLiteral p = toCNF(node[0], false);
    SatLiteral q = toCNF(node[1], false);
    // Construct the clauses (p => !q) and (!q => p)
    SatClause clause1(2);
    clause1[0] = ~p;
    clause1[1] = ~q;
    assertClause(node, clause1);
    SatClause clause2(2);
    clause2[0] = p;
    clause2[1] = q;
    assertClause(node, clause2);
  }
  else
  {
    // !(p XOR q) is the same as p <=> q
    SatLiteral p = toCNF(node[0], false);
    SatLiteral q = toCNF(node[1], false);
    // Construct the clauses (p => q) and (q => p)
    SatClause clause1(2);
    clause1[0] = ~p;
    clause1[1] = q;
    assertClause(node.negate(), clause1);
    SatClause clause2(2);
    clause2[0] = p;
    clause2[1] = ~q;
    assertClause(node.negate(), clause2);
  }
}

void CnfStream::convertAndAssertIff(TNode node, bool negated, bool root)
{
  Assert(node.getKind() == Kind::EQUAL);
  Trace("cnf") << "CnfStream::convertAndAssertIff(" << node
               << ", negated = " << (negated ? "true" : "false")
               << ", root = " << (root ? "true" : "false")
               << ")\n";
  if (!negated)
  {
    // p <=> q
    SatLiteral p = toCNF(node[0], false);
    SatLiteral q = toCNF(node[1], false);
    // Construct the clauses (p => q) and (q => p)
    SatClause clause1(2);
    clause1[0] = ~p;
    clause1[1] = q;
    assertClause(node, clause1);
    SatClause clause2(2);
    clause2[0] = p;
    clause2[1] = ~q;
    assertClause(node, clause2);
  }
  else
  {
    // !(p <=> q) is the same as p XOR q
    SatLiteral p = toCNF(node[0], false);
    SatLiteral q = toCNF(node[1], false);
    // Construct the clauses (p => !q) and (!q => p)
    SatClause clause1(2);
    clause1[0] = ~p;
    clause1[1] = ~q;
    assertClause(node.negate(), clause1);
    SatClause clause2(2);
    clause2[0] = p;
    clause2[1] = q;
    assertClause(node.negate(), clause2);
  }
}

void CnfStream::convertAndAssertImplies(TNode node, bool negated, bool root)
{
  Assert(node.getKind() == Kind::IMPLIES);
  Trace("cnf") << "CnfStream::convertAndAssertImplies(" << node
               << ", negated = " << (negated ? "true" : "false")
               << ", root = " << (root ? "true" : "false")
               << ")\n";
  std::vector<int64_t> aigliterals;

  if (!negated)
  {
    // p => q
    SatLiteral p = toCNF(node[0], false);
    SatLiteral q = toCNF(node[1], false);

    int64_t p_a = getAIGliteral(p, node[0]);
    int64_t q_a = getAIGliteral(q, node[1]);
    int64_t t_1 = newAIGVar(false);

    // Construct the clause ~p || q
    SatClause clause(2);
    clause[0] = ~p;
    clause[1] = q;
    assertClause(node, clause);

    aigliterals.push_back(t_1);
    aigliterals.push_back(p_a);
    aigliterals.push_back(negateAIGVar(q_a));
    aigGateLines.push_back(aigliterals);
    aigAssertLits.push_back(negateAIGVar(t_1));
    aigliterals.clear();
  }
  else
  {  // Construct the
    // !(p => q) is the same as (p && ~q)
    convertAndAssert(node[0], false, false);
    convertAndAssert(node[1], true, false);
  }
}

void CnfStream::convertAndAssertIte(TNode node, bool negated, bool root)
{
  Assert(node.getKind() == Kind::ITE);
  Trace("cnf") << "CnfStream::convertAndAssertIte(" << node
               << ", negated = " << (negated ? "true" : "false")
               << ", root = " << (root ? "true" : "false")
               << ")\n";
  std::vector<int64_t> aigliterals;
  int64_t p_a, q_a, r_a, t_1, t_2;
  int64_t aigOutputVar;
  if (root)
  {
    aigOutputVar = newAIGVar(true);
    Trace("aiginfo") << "ITE gate root " << aigOutputVar << std::endl;
    aigAssertLits.push_back(aigOutputVar);
  }
  // ITE(p, q, r)
  SatLiteral p = toCNF(node[0], false);
  SatLiteral q = toCNF(node[1], negated);
  SatLiteral r = toCNF(node[2], negated);

  p_a = getAIGliteral(p, node[0]);
  q_a = getAIGliteral(q, node[1]);
  r_a = getAIGliteral(r, node[2]);

  t_1 = newAIGVar(false);
  t_2 = newAIGVar(false);

  // Construct the clauses:
  // (p => q) and (!p => r)
  //
  // Note that below q and r can be used directly because whether they are
  // negated has been push to the literal definitions above
  Node nnode = node;
  if (negated)
  {
    nnode = node.negate();
  }
  SatClause clause1(2);
  clause1[0] = ~p;
  clause1[1] = q;
  assertClause(nnode, clause1);
  SatClause clause2(2);
  clause2[0] = p;
  clause2[1] = r;
  assertClause(nnode, clause2);

  // Construct the AIG gates
  // t_1 = (p & q)
  // t_2 = (!p & r)
  // out = (!t_1 & !t_2)


  aigliterals.push_back(t_1);
  aigliterals.push_back(p_a);
  aigliterals.push_back(q_a);
  aigGateLines.push_back(aigliterals);
  aigliterals.clear();

  aigliterals.push_back(t_2);
  aigliterals.push_back(negateAIGVar(p_a));
  aigliterals.push_back(r_a);
  aigGateLines.push_back(aigliterals);
  aigliterals.clear();

  aigliterals.push_back(aigOutputVar);
  aigliterals.push_back(negateAIGVar(t_1));
  aigliterals.push_back(negateAIGVar(t_2));
  aigGateLines.push_back(aigliterals);

  printAigGateLines("convertAndAssertIte");
}

// At the top level we must ensure that all clauses that are asserted are
// not unit, except for the direct assertions. This allows us to remove the
// clauses later when they are not needed anymore (lemmas for example).
void CnfStream::convertAndAssert(TNode node, bool removable, bool negated, bool root)
{
  Trace("cnf") << "convertAndAssert(" << node
               << ", negated = " << (negated ? "true" : "false")
               << ", removable = " << (removable ? "true" : "false")
               << ", root = " << (root ? "true" : "false")
               << ")\n";
  d_removable = removable;

  TimerStat::CodeTimer codeTimer(d_stats.d_cnfConversionTime, true);
  convertAndAssert(node, negated, root);
}

void CnfStream::convertAndAssert(TNode node, bool negated, bool root)
{
  Trace("cnf") << "convertAndAssertX(" << node
               << ", negated = " << (negated ? "true" : "false")
                << ", root = " << (root ? "true" : "false")
               << ")\n";

  resourceManager()->spendResource(Resource::CnfStep);

  switch (node.getKind())
  {
    case Kind::AND: convertAndAssertAnd(node, negated, root); break;
    case Kind::OR: convertAndAssertOr(node, negated, root); break;
    case Kind::XOR: convertAndAssertXor(node, negated, root); break;
    case Kind::IMPLIES: convertAndAssertImplies(node, negated, root); break;
    case Kind::ITE: convertAndAssertIte(node, negated, root); break;
    case Kind::NOT: convertAndAssert(node[0], false, !negated, root); break;
    case Kind::EQUAL:
      if (node[0].getType().isBoolean())
      {
        convertAndAssertIff(node, negated, root);
        break;
      }
      CVC5_FALLTHROUGH;
    default:
    {
      Node nnode = node;
      if (negated)
      {
        nnode = node.negate();
      }
      // Atoms
      auto literal = toCNF(node, negated);
      assertClause(nnode, literal);
      if (root)
      {
        int64_t aigAssertLit = getAIGliteral(literal, node, false, false);
        aigAssertLits.push_back(aigAssertLit);
        Trace("aiginfo") << "Setting as assert lit root atom: " << aigAssertLit  << " for node " << node << " which is negated? " << negated  << std::endl;
      }
    }
    break;
  }
}

CnfStream::Statistics::Statistics(StatisticsRegistry& sr,
                                  const std::string& name)
    : d_cnfConversionTime(
          sr.registerTimer(name + "::CnfStream::cnfConversionTime")),
      d_numAtoms(sr.registerInt(name + "::CnfStream::numAtoms"))
{
}

void CnfStream::dumpDimacs(std::ostream& out, const std::vector<Node>& clauses)
{
  std::vector<Node> auxUnits;
  dumpDimacs(out, clauses, auxUnits);
}

void CnfStream::dumpDimacs(std::ostream& out,
                           const std::vector<Node>& clauses,
                           const std::vector<Node>& auxUnits)
{
  std::stringstream dclauses;
  SatVariable maxVar = 0;
  for (size_t j = 0; j < 2; j++)
  {
    const std::vector<Node>& cls = j == 0 ? clauses : auxUnits;
    for (const Node& i : cls)
    {
      std::vector<Node> lits;
      if (j == 0 && i.getKind() == Kind::OR)
      {
        // print as clause if not an auxiliary unit
        lits.insert(lits.end(), i.begin(), i.end());
      }
      else
      {
        lits.push_back(i);
      }
      Trace("dimacs-debug") << "Print " << i << std::endl;
      for (const Node& l : lits)
      {
        bool negated = l.getKind() == Kind::NOT;
        const Node& atom = negated ? l[0] : l;
        SatLiteral lit = getLiteral(atom);
        SatVariable v = lit.getSatVariable();
        maxVar = v > maxVar ? v : maxVar;
        dclauses << (negated ? "-" : "") << v << " ";
      }
      dclauses << "0" << std::endl;
    }
  }

  out << "p cnf " << maxVar << " " << (clauses.size() + auxUnits.size())
      << std::endl;
  out << dclauses.str();
}

}  // namespace prop
}  // namespace cvc5::internal
