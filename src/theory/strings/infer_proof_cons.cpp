/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of inference to proof conversion.
 */

#include "theory/strings/infer_proof_cons.h"

#include "expr/skolem_manager.h"
#include "options/smt_options.h"
#include "options/strings_options.h"
#include "proof/proof_node_manager.h"
#include "theory/builtin/proof_checker.h"
#include "theory/rewriter.h"
#include "theory/strings/regexp_operation.h"
#include "theory/strings/theory_strings_utils.h"
#include "util/statistics_registry.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace strings {

InferProofCons::InferProofCons(Env& env,
                               context::Context* c,
                               SequencesStatistics& statistics)
    : EnvObj(env), d_lazyFactMap(c), d_statistics(statistics)
{
}

void InferProofCons::notifyFact(const InferInfo& ii)
{
  Node fact = ii.d_conc;
  Trace("strings-ipc-debug")
      << "InferProofCons::notifyFact: " << ii << std::endl;
  if (d_lazyFactMap.find(fact) != d_lazyFactMap.end())
  {
    Trace("strings-ipc-debug") << "...duplicate!" << std::endl;
    return;
  }
  Node symFact = CDProof::getSymmFact(fact);
  if (!symFact.isNull() && d_lazyFactMap.find(symFact) != d_lazyFactMap.end())
  {
    Trace("strings-ipc-debug") << "...duplicate (sym)!" << std::endl;
    return;
  }
  std::shared_ptr<InferInfo> iic = std::make_shared<InferInfo>(ii);
  d_lazyFactMap.insert(ii.d_conc, iic);
}

void InferProofCons::notifyLemma(const InferInfo& ii)
{
  d_lazyFactMap[ii.d_conc] = std::make_shared<InferInfo>(ii);
}

bool InferProofCons::convertAndAddProofTo(CDProof* pf,
                                          Node conc,
                                          InferenceId infer,
                                          bool isRev,
                                          const std::vector<Node>& exp)
{
  // now go back and convert it to proof steps and add to proof
  bool useBuffer = false;
  ProofStep ps;
  // ensure proof steps are unique
  TheoryProofStepBuffer psb(pf->getManager()->getChecker(), true);
  // run the conversion
  convert(infer, isRev, conc, exp, ps, psb, useBuffer);
  // make the proof based on the step or the buffer
  if (useBuffer)
  {
    if (!pf->addSteps(psb))
    {
      return false;
    }
  }
  else
  {
    if (!pf->addStep(conc, ps))
    {
      return false;
    }
  }
  return true;
}

void InferProofCons::packArgs(Node conc,
                              InferenceId infer,
                              bool isRev,
                              const std::vector<Node>& exp,
                              std::vector<Node>& args)
{
  args.push_back(conc);
  args.push_back(mkInferenceIdNode(infer));
  args.push_back(NodeManager::currentNM()->mkConst(isRev));
  // The vector exp is stored as arguments; its flatten form are premises. We
  // need both since the grouping of exp is important, e.g. { (and a b), c }
  // is different from { a, b, c } in the convert routine, since positions
  // of formulas in exp have special meaning.
  args.insert(args.end(), exp.begin(), exp.end());
}

bool InferProofCons::unpackArgs(const std::vector<Node>& args,
                                Node& conc,
                                InferenceId& infer,
                                bool& isRev,
                                std::vector<Node>& exp)
{
  Assert(args.size() >= 3);
  conc = args[0];
  if (!getInferenceId(args[1], infer))
  {
    return false;
  }
  isRev = args[2].getConst<bool>();
  exp.insert(exp.end(), args.begin() + 3, args.end());
  return true;
}

void InferProofCons::convert(InferenceId infer,
                             bool isRev,
                             Node conc,
                             const std::vector<Node>& exp,
                             ProofStep& ps,
                             TheoryProofStepBuffer& psb,
                             bool& useBuffer)
{
  // by default, don't use the buffer
  useBuffer = false;
  // Must flatten children with respect to AND to be ready to explain.
  // We store the index where each flattened vector begins, since some
  // explanations are grouped together using AND.
  std::vector<size_t> startExpIndex;
  for (const Node& ec : exp)
  {
    // store the index in the flattened vector
    startExpIndex.push_back(ps.d_children.size());
    utils::flattenOp(Kind::AND, ec, ps.d_children);
  }
  // debug print
  if (TraceIsOn("strings-ipc-debug"))
  {
    Trace("strings-ipc-debug") << "InferProofCons::convert: " << infer
                               << (isRev ? " :rev " : " ") << conc << std::endl;
    for (const Node& ec : ps.d_children)
    {
      Trace("strings-ipc-debug") << "    e: " << ec << std::endl;
    }
  }
  // try to find a set of proof steps to incorporate into the buffer
  psb.clear();
  // explicitly add ASSUME steps to the proof step buffer for premises of the
  // inference, so that they will not be overwritten in the reconstruction
  // below
  for (const Node& ec : ps.d_children)
  {
    Trace("strings-ipc-debug") << "Explicit add " << ec << std::endl;
    psb.addStep(ProofRule::ASSUME, {}, {ec}, ec);
  }
  NodeManager* nm = NodeManager::currentNM();
  Node nodeIsRev = nm->mkConst(isRev);
  switch (infer)
  {
    // ========================== equal by substitution+rewriting
    case InferenceId::STRINGS_EXTF:
    case InferenceId::STRINGS_EXTF_N:
    case InferenceId::STRINGS_I_NORM_S:
    case InferenceId::STRINGS_I_CONST_MERGE:
    case InferenceId::STRINGS_I_NORM:
    case InferenceId::STRINGS_LEN_NORM:
    case InferenceId::STRINGS_NORMAL_FORM:
    case InferenceId::STRINGS_CODE_PROXY:
    {
      PurifyType pt = PurifyType::CORE_EQ;
      if (infer == InferenceId::STRINGS_EXTF
          || infer == InferenceId::STRINGS_EXTF_N)
      {
        // since we use congruence+rewriting, and not substitution+rewriting,
        // these must purify a substitution over arguments to the left hand
        // side of what we are proving.
        pt = PurifyType::EXTF;
      }
      std::vector<Node> pcs = ps.d_children;
      Node pconc = conc;
      // purify core substitution proves conc from pconc if necessary,
      // we apply MACRO_SR_PRED_INTRO to prove pconc
      if (purifyCoreSubstitutionAndTarget(pt, pconc, pcs, psb, false))
      {
        Trace("strings-ipc-core") << "...purified substitution to " << pcs
                                  << ", now apply to " << pconc << std::endl;
        if (psb.applyPredIntro(pconc, pcs))
        {
          useBuffer = true;
        }
      }
      else
      {
        Trace("strings-ipc-core")
            << "...failed to purify substitution" << std::endl;
      }
    }
    break;
    // ========================== substitution + rewriting
    case InferenceId::STRINGS_RE_NF_CONFLICT:
    case InferenceId::STRINGS_EXTF_D:
    case InferenceId::STRINGS_EXTF_D_N:
    case InferenceId::STRINGS_I_CONST_CONFLICT:
    case InferenceId::STRINGS_UNIT_CONST_CONFLICT:
    case InferenceId::STRINGS_ARITH_BOUND_CONFLICT:
    {
      if (!ps.d_children.empty())
      {
        std::vector<Node> exps(ps.d_children.begin(), ps.d_children.end() - 1);
        Node psrc = ps.d_children[ps.d_children.size() - 1];
        // we apply the substitution on the purified form to get the
        // original conclusion
        if (psb.applyPredTransform(psrc, conc, exps))
        {
          useBuffer = true;
        }
        else
        {
          // More aggressive: lift to original form and use extended rewriting.
          // A common case that this covers is arithmetic bound conflicts like
          // (= (str.len @purifyN) 5) where @purifyN is the purification skolem
          // for (str.++ "ABCDEF" x).
          Node psrco = SkolemManager::getOriginalForm(psrc);
          if (psb.applyPredTransform(psrco,
                                     conc,
                                     exps,
                                     MethodId::SB_DEFAULT,
                                     MethodId::SBA_SEQUENTIAL,
                                     MethodId::RW_EXT_REWRITE))
          {
            useBuffer = psb.applyPredTransform(psrc, psrco, {});
          }
        }
      }
      else
      {
        // use the predicate version?
        ps.d_args.push_back(conc);
        ps.d_rule = ProofRule::MACRO_SR_PRED_INTRO;
      }
    }
    break;
    // ========================== rewrite pred
    case InferenceId::STRINGS_EXTF_EQ_REW:
    {
      // the last child is the predicate we are operating on, move to front
      Node src = ps.d_children[ps.d_children.size() - 1];
      std::vector<Node> expe(ps.d_children.begin(), ps.d_children.end() - 1);
      // start with a default rewrite
      Trace("strings-ipc-core")
          << "Generate proof for STRINGS_EXTF_EQ_REW, starting with " << src
          << std::endl;
      Node mainEqSRew = psb.applyPredElim(src, expe);
      Trace("strings-ipc-core")
          << "...after pred elim: " << mainEqSRew << std::endl;
      if (mainEqSRew == conc)
      {
        Trace("strings-ipc-core") << "...success" << std::endl;
        useBuffer = true;
        break;
      }
      else if (mainEqSRew.getKind() != Kind::EQUAL)
      {
        // Note this can happen in rare cases where substitution+rewriting
        // is more powerful than congruence+rewriting. We fail to reconstruct
        // the proof in this case.
        Trace("strings-ipc-core")
            << "...failed, not equality after rewriting" << std::endl;
        break;
      }
      // may need the "extended equality rewrite"
      Node mainEqSRew2 = psb.applyPredElim(mainEqSRew,
                                           {},
                                           MethodId::SB_DEFAULT,
                                           MethodId::SBA_SEQUENTIAL,
                                           MethodId::RW_REWRITE_EQ_EXT);
      Trace("strings-ipc-core")
          << "...after extended equality rewrite: " << mainEqSRew2 << std::endl;
      if (mainEqSRew2 == conc)
      {
        useBuffer = true;
        break;
      }
      // rewrite again with default rewriter
      Node mainEqSRew3 = psb.applyPredElim(mainEqSRew2, {});
      useBuffer = (mainEqSRew3 == conc);
    }
    break;
    // ========================== extensionality
    case InferenceId::STRINGS_DEQ_EXTENSIONALITY:
    {
      ps.d_rule = ProofRule::STRING_EXT;
    }
    break;
    // ========================== substitution+rewriting, CONCAT_EQ, ...
    case InferenceId::STRINGS_F_CONST:
    case InferenceId::STRINGS_F_UNIFY:
    case InferenceId::STRINGS_F_ENDPOINT_EMP:
    case InferenceId::STRINGS_F_ENDPOINT_EQ:
    case InferenceId::STRINGS_F_NCTN:
    case InferenceId::STRINGS_N_EQ_CONF:
    case InferenceId::STRINGS_N_CONST:
    case InferenceId::STRINGS_N_UNIFY:
    case InferenceId::STRINGS_N_ENDPOINT_EMP:
    case InferenceId::STRINGS_N_ENDPOINT_EQ:
    case InferenceId::STRINGS_N_NCTN:
    case InferenceId::STRINGS_SSPLIT_CST_PROP:
    case InferenceId::STRINGS_SSPLIT_VAR_PROP:
    case InferenceId::STRINGS_SSPLIT_CST:
    case InferenceId::STRINGS_SSPLIT_VAR:
    {
      Trace("strings-ipc-core") << "Generate core rule for " << infer
                                << " (rev=" << isRev << ")" << std::endl;
      // All of the above inferences have the form:
      //   (explanation for why t and s have the same prefix/suffix) ^
      //   t = s ^
      //   (length constraint)?
      // We call t=s the "main equality" below. The length constraint is
      // optional, which we split on below.
      size_t nchild = ps.d_children.size();
      size_t mainEqIndex = 0;
      bool mainEqIndexSet = false;
      // the length constraint
      std::vector<Node> lenConstraint;
      // these inferences have a length constraint as the last explain
      if (infer == InferenceId::STRINGS_N_UNIFY || infer == InferenceId::STRINGS_F_UNIFY
          || infer == InferenceId::STRINGS_SSPLIT_CST || infer == InferenceId::STRINGS_SSPLIT_VAR
          || infer == InferenceId::STRINGS_SSPLIT_VAR_PROP
          || infer == InferenceId::STRINGS_SSPLIT_CST_PROP)
      {
        if (exp.size() >= 2)
        {
          Assert(exp.size() <= startExpIndex.size());
          // The index of the "main" equality is the last equality before
          // the length explanation.
          mainEqIndex = startExpIndex[exp.size() - 1] - 1;
          mainEqIndexSet = true;
          // the remainder is the length constraint
          lenConstraint.insert(lenConstraint.end(),
                               ps.d_children.begin() + mainEqIndex + 1,
                               ps.d_children.end());
        }
      }
      else if (nchild >= 1)
      {
        // The index of the main equality is the last child.
        mainEqIndex = nchild - 1;
        mainEqIndexSet = true;
      }
      Node mainEq;
      if (mainEqIndexSet)
      {
        mainEq = ps.d_children[mainEqIndex];
        Trace("strings-ipc-core") << "Main equality " << mainEq << " at index "
                                  << mainEqIndex << std::endl;
      }
      if (mainEq.isNull() || mainEq.getKind() != Kind::EQUAL)
      {
        Trace("strings-ipc-core")
            << "...failed to find main equality" << std::endl;
        break;
      }
      // apply MACRO_SR_PRED_ELIM using equalities up to the main eq
      // we purify the core substitution
      std::vector<Node> pcsr(ps.d_children.begin(),
                             ps.d_children.begin() + mainEqIndex);
      Node pmainEq = mainEq;
      // we transform mainEq to pmainEq and then use this as the first
      // argument to MACRO_SR_PRED_ELIM.
      if (!purifyCoreSubstitutionAndTarget(
              PurifyType::CORE_EQ, pmainEq, pcsr, psb, true))
      {
        break;
      }
      Trace("strings-ipc-core")
          << "Main equality after purify " << pmainEq << std::endl;
      std::vector<Node> childrenSRew;
      childrenSRew.push_back(pmainEq);
      childrenSRew.insert(childrenSRew.end(), pcsr.begin(), pcsr.end());
      // now, conclude the proper equality
      Node mainEqSRew =
          psb.tryStep(ProofRule::MACRO_SR_PRED_ELIM, childrenSRew, {});
      if (mainEqSRew == conc)
      {
        Trace("strings-ipc-core") << "...success after rewrite!" << std::endl;
        useBuffer = true;
        break;
      }
      Trace("strings-ipc-core")
          << "Main equality after subs+rewrite " << mainEqSRew << std::endl;
      // now, apply CONCAT_EQ to get the remainder
      std::vector<Node> childrenCeq;
      childrenCeq.push_back(mainEqSRew);
      std::vector<Node> argsCeq;
      argsCeq.push_back(nodeIsRev);
      Node mainEqCeq = psb.tryStep(ProofRule::CONCAT_EQ, childrenCeq, argsCeq);
      Trace("strings-ipc-core")
          << "Main equality after CONCAT_EQ " << mainEqCeq << std::endl;
      if (mainEqCeq.isNull() || mainEqCeq.getKind() != Kind::EQUAL)
      {
        // fail
        break;
      }
      // get the heads of the equality
      std::vector<Node> tvec;
      std::vector<Node> svec;
      theory::strings::utils::getConcat(mainEqCeq[0], tvec);
      theory::strings::utils::getConcat(mainEqCeq[1], svec);
      Node t0 = tvec[isRev ? tvec.size() - 1 : 0];
      Node s0 = svec[isRev ? svec.size() - 1 : 0];
      // Now, mainEqCeq is an equality t ++ ... == s ++ ... where the
      // inference involved t and s.
      if (infer == InferenceId::STRINGS_N_ENDPOINT_EQ
          || infer == InferenceId::STRINGS_N_ENDPOINT_EMP
          || infer == InferenceId::STRINGS_F_ENDPOINT_EQ
          || infer == InferenceId::STRINGS_F_ENDPOINT_EMP)
      {
        // Should be equal to conclusion already, or rewrite to it.
        // Notice that this step is necessary to handle the "rproc"
        // optimization in processSimpleNEq. Alternatively, this could
        // possibly be done by CONCAT_EQ with !isRev.
        std::vector<Node> cexp;
        if (psb.applyPredTransform(mainEqCeq,
                                   conc,
                                   cexp,
                                   MethodId::SB_DEFAULT,
                                   MethodId::SBA_SEQUENTIAL,
                                   MethodId::RW_REWRITE_EQ_EXT))
        {
          Trace("strings-ipc-core") << "Transformed to " << conc
                                    << " via pred transform" << std::endl;
          // success
          useBuffer = true;
          Trace("strings-ipc-core") << "...success!" << std::endl;
        }
        // Otherwise, note that EMP rules conclude ti = "" where
        // t1 ++ ... ++ tn == "". However, these are very rarely applied, let
        // alone for 2+ children. This case is intentionally unhandled here.
      }
      else if (infer == InferenceId::STRINGS_N_CONST || infer == InferenceId::STRINGS_F_CONST
               || infer == InferenceId::STRINGS_N_EQ_CONF)
      {
        // should be a constant conflict
        std::vector<Node> childrenC;
        childrenC.push_back(mainEqCeq);
        // if it is between sequences, we require the explicit disequality
        ProofRule r = ProofRule::CONCAT_CONFLICT;
        if (mainEqCeq[0].getType().isSequence())
        {
          Assert(t0.isConst() && s0.isConst());
          // We introduce an explicit disequality for the constants
          Node deq = t0.eqNode(s0).notNode();
          psb.addStep(ProofRule::MACRO_SR_PRED_INTRO, {}, {deq}, deq);
          Assert(!deq.isNull());
          childrenC.push_back(deq);
          r = ProofRule::CONCAT_CONFLICT_DEQ;
        }
        std::vector<Node> argsC;
        argsC.push_back(nodeIsRev);
        Node conflict = psb.tryStep(r, childrenC, argsC);
        if (conflict == conc)
        {
          useBuffer = true;
          Trace("strings-ipc-core") << "...success!" << std::endl;
        }
      }
      else if (infer == InferenceId::STRINGS_F_NCTN
               || infer == InferenceId::STRINGS_N_NCTN)
      {
        // May require extended equality rewrite, applied after the rewrite
        // above. Notice we need both in sequence since ext equality rewriting
        // is not recursive.
        std::vector<Node> argsERew;
        addMethodIds(argsERew,
                     MethodId::SB_DEFAULT,
                     MethodId::SBA_SEQUENTIAL,
                     MethodId::RW_REWRITE_EQ_EXT);
        Node mainEqERew =
            psb.tryStep(ProofRule::MACRO_SR_PRED_ELIM, {mainEqCeq}, argsERew);
        if (mainEqERew == conc)
        {
          useBuffer = true;
          Trace("strings-ipc-core") << "...success!" << std::endl;
        }
      }
      else
      {
        bool applySym = false;
        // may need to apply symmetry
        if ((infer == InferenceId::STRINGS_SSPLIT_CST
             || infer == InferenceId::STRINGS_SSPLIT_CST_PROP)
            && t0.isConst())
        {
          Assert(!s0.isConst());
          applySym = true;
          std::swap(t0, s0);
        }
        if (infer == InferenceId::STRINGS_N_UNIFY || infer == InferenceId::STRINGS_F_UNIFY)
        {
          if (conc.getKind() != Kind::EQUAL)
          {
            break;
          }
          // one side should match, the other side could be a split constant
          if (conc[0] != t0 && conc[1] != s0)
          {
            applySym = true;
            std::swap(t0, s0);
          }
          Assert(conc[0].isConst() == t0.isConst());
          Assert(conc[1].isConst() == s0.isConst());
        }
        ProofRule rule = ProofRule::UNKNOWN;
        // the form of the required length constraint expected by the proof
        Node lenReq;
        bool lenSuccess = false;
        if (infer == InferenceId::STRINGS_N_UNIFY || infer == InferenceId::STRINGS_F_UNIFY)
        {
          // the required premise for unify is always len(x) = len(y),
          // however the explanation may not be literally this. Thus, we
          // need to reconstruct a proof from the given explanation.
          // it should be the case that lenConstraint => lenReq.
          // We use terms in the conclusion equality, not t0, s0 here.
          lenReq = nm->mkNode(Kind::STRING_LENGTH, conc[0])
                       .eqNode(nm->mkNode(Kind::STRING_LENGTH, conc[1]));
          lenSuccess = convertLengthPf(lenReq, lenConstraint, psb);
          rule = ProofRule::CONCAT_UNIFY;
        }
        else if (infer == InferenceId::STRINGS_SSPLIT_VAR)
        {
          // it should be the case that lenConstraint => lenReq
          lenReq = nm->mkNode(Kind::STRING_LENGTH, t0)
                       .eqNode(nm->mkNode(Kind::STRING_LENGTH, s0))
                       .notNode();
          lenSuccess = convertLengthPf(lenReq, lenConstraint, psb);
          rule = ProofRule::CONCAT_SPLIT;
        }
        else if (infer == InferenceId::STRINGS_SSPLIT_CST)
        {
          // it should be the case that lenConstraint => lenReq
          lenReq = nm->mkNode(Kind::STRING_LENGTH, t0)
                       .eqNode(nm->mkConstInt(Rational(0)))
                       .notNode();
          lenSuccess = convertLengthPf(lenReq, lenConstraint, psb);
          rule = ProofRule::CONCAT_CSPLIT;
        }
        else if (infer == InferenceId::STRINGS_SSPLIT_VAR_PROP)
        {
          // it should be the case that lenConstraint => lenReq
          for (unsigned r = 0; r < 2; r++)
          {
            lenReq = nm->mkNode(Kind::GT,
                                nm->mkNode(Kind::STRING_LENGTH, t0),
                                nm->mkNode(Kind::STRING_LENGTH, s0));
            if (convertLengthPf(lenReq, lenConstraint, psb))
            {
              lenSuccess = true;
              break;
            }
            if (r == 0)
            {
              // may be the other direction
              applySym = true;
              std::swap(t0, s0);
            }
          }
          rule = ProofRule::CONCAT_LPROP;
        }
        else if (infer == InferenceId::STRINGS_SSPLIT_CST_PROP)
        {
          // it should be the case that lenConstraint => lenReq
          lenReq = nm->mkNode(Kind::STRING_LENGTH, t0)
                       .eqNode(nm->mkConstInt(Rational(0)))
                       .notNode();
          lenSuccess = convertLengthPf(lenReq, lenConstraint, psb);
          rule = ProofRule::CONCAT_CPROP;
        }
        if (!lenSuccess)
        {
          Trace("strings-ipc-core")
              << "...failed due to length constraint" << std::endl;
          break;
        }
        // apply symmetry if necessary
        if (applySym)
        {
          std::vector<Node> childrenSymm;
          childrenSymm.push_back(mainEqCeq);
          // note this explicit step may not be necessary
          mainEqCeq = psb.tryStep(ProofRule::SYMM, childrenSymm, {});
          Trace("strings-ipc-core")
              << "Main equality after SYMM " << mainEqCeq << std::endl;
        }
        if (rule != ProofRule::UNKNOWN)
        {
          Trace("strings-ipc-core")
              << "Core rule length requirement is " << lenReq << std::endl;
          // apply the given rule
          std::vector<Node> childrenMain;
          childrenMain.push_back(mainEqCeq);
          childrenMain.push_back(lenReq);
          std::vector<Node> argsMain;
          argsMain.push_back(nodeIsRev);
          Node mainEqMain = psb.tryStep(rule, childrenMain, argsMain);
          Trace("strings-ipc-core") << "Main equality after " << rule << " "
                                    << mainEqMain << std::endl;
          // either equal or rewrites to it
          std::vector<Node> cexp;
          if (psb.applyPredTransform(mainEqMain, conc, cexp))
          {
            // requires that length success is also true
            useBuffer = true;
            Trace("strings-ipc-core") << "...success" << std::endl;
          }
          else
          {
            Trace("strings-ipc-core") << "...fail" << std::endl;
          }
        }
        else
        {
          // should always have given a rule to try above
          Assert(false) << "No reconstruction rule given for " << infer;
        }
      }
    }
    break;
    // ========================== Disequalities
    case InferenceId::STRINGS_DEQ_DISL_FIRST_CHAR_STRING_SPLIT:
    case InferenceId::STRINGS_DEQ_DISL_STRINGS_SPLIT:
    {
      if (conc.getKind() != Kind::AND || conc.getNumChildren() != 2
          || conc[0].getKind() != Kind::EQUAL
          || !conc[0][0].getType().isStringLike()
          || conc[1].getKind() != Kind::EQUAL
          || conc[1][0].getKind() != Kind::STRING_LENGTH)
      {
        Trace("strings-ipc-deq") << "malformed application" << std::endl;
        Assert(false) << "unexpected conclusion " << conc << " for " << infer;
      }
      else
      {
        Node lenReq = nm->mkNode(
            Kind::GEQ, nm->mkNode(Kind::STRING_LENGTH, conc[0][0]), conc[1][1]);
        Trace("strings-ipc-deq")
            << "length requirement is " << lenReq << std::endl;
        if (convertLengthPf(lenReq, ps.d_children, psb))
        {
          Trace("strings-ipc-deq") << "...success length" << std::endl;
          // make the proof
          std::vector<Node> childrenMain;
          childrenMain.push_back(lenReq);
          std::vector<Node> argsMain;
          argsMain.push_back(nodeIsRev);
          Node mainConc =
              psb.tryStep(ProofRule::STRING_DECOMPOSE, childrenMain, argsMain);
          Trace("strings-ipc-deq")
              << "...main conclusion is " << mainConc << std::endl;
          useBuffer = (mainConc == conc);
          if (!useBuffer)
          {
            // Should be made equal by transformation. This step is necessary
            // if rewriting was used to change the skolem introduced in the
            // conclusion.
            useBuffer = psb.applyPredTransform(mainConc, conc, {});
          }
          Trace("strings-ipc-deq")
              << "...success is " << useBuffer << std::endl;
        }
        else
        {
          Assert(false)
              << "Failed to convert length " << lenReq << " " << ps.d_children;
          Trace("strings-ipc-deq") << "...fail length" << std::endl;
        }
      }
    }
    break;
    // ========================== Boolean split
    case InferenceId::STRINGS_CARD_SP:
    case InferenceId::STRINGS_LEN_SPLIT:
    case InferenceId::STRINGS_LEN_SPLIT_EMP:
    case InferenceId::STRINGS_DEQ_DISL_EMP_SPLIT:
    case InferenceId::STRINGS_DEQ_DISL_FIRST_CHAR_EQ_SPLIT:
    case InferenceId::STRINGS_DEQ_STRINGS_EQ:
    case InferenceId::STRINGS_DEQ_LENS_EQ:
    case InferenceId::STRINGS_DEQ_LENGTH_SP:
    case InferenceId::STRINGS_UNIT_SPLIT:
    {
      if (conc.getKind() != Kind::OR)
      {
        // This should never happen. If it does, we resort to using
        // THEORY_INFERENCE below (in production mode).
        Assert(false) << "Expected OR conclusion for " << infer;
      }
      else
      {
        ps.d_rule = ProofRule::SPLIT;
        Assert(ps.d_children.empty());
        ps.d_args.push_back(conc[0]);
      }
    }
    break;
    // ========================== Regular expression unfolding
    case InferenceId::STRINGS_RE_UNFOLD_POS:
    case InferenceId::STRINGS_RE_UNFOLD_NEG:
    {
      Assert (!ps.d_children.empty());
      size_t nchild = ps.d_children.size();
      Node mem = ps.d_children[nchild-1];
      if (nchild>1)
      {
        // if more than one, apply MACRO_SR_PRED_ELIM
        std::vector<Node> tcs;
        tcs.insert(tcs.end(),
                          ps.d_children.begin(),
                          ps.d_children.begin() + (nchild-1));
        mem = psb.applyPredElim(mem, tcs);
        useBuffer = true;
      }
      ProofRule r = ProofRule::UNKNOWN;
      std::vector<Node> args;
      if (mem.isNull())
      {
        // failed to eliminate above
        Assert(false) << "Failed to apply MACRO_SR_PRED_ELIM for RE unfold";
        useBuffer = false;
      }
      else if (infer == InferenceId::STRINGS_RE_UNFOLD_POS)
      {
        r = ProofRule::RE_UNFOLD_POS;
      }
      else
      {
        r = ProofRule::RE_UNFOLD_NEG;
        // it may be an optimized form of concat simplification
        Assert(mem.getKind() == Kind::NOT
               && mem[0].getKind() == Kind::STRING_IN_REGEXP);
        if (mem[0][1].getKind() == Kind::REGEXP_CONCAT)
        {
          bool isCRev;
          Node reLen = RegExpOpr::getRegExpConcatFixed(mem[0][1], isCRev);
          // if we can find a fixed length for a component, use the optimized
          // version
          if (!reLen.isNull())
          {
            r = ProofRule::RE_UNFOLD_NEG_CONCAT_FIXED;
            args.push_back(nm->mkConst(isCRev));
          }
        }
      }
      if (useBuffer)
      {
        mem = psb.tryStep(r, {mem}, args);
        // should match the conclusion
        useBuffer = (mem==conc);
      }
      else
      {
        ps.d_rule = r;
        ps.d_args = args;
      }
    }
    break;
    // ========================== Reduction
    case InferenceId::STRINGS_CTN_POS:
    case InferenceId::STRINGS_CTN_NEG_EQUAL:
    {
      if (ps.d_children.size() != 1)
      {
        break;
      }
      bool polarity = ps.d_children[0].getKind() != Kind::NOT;
      Node atom = polarity ? ps.d_children[0] : ps.d_children[0][0];
      std::vector<Node> args;
      args.push_back(atom);
      Node res = psb.tryStep(ProofRule::STRING_EAGER_REDUCTION, {}, args);
      if (res.isNull())
      {
        break;
      }
      // ite( contains(x,t), x = k1 ++ t ++ k2, x != t )
      std::vector<Node> tiChildren;
      tiChildren.push_back(ps.d_children[0]);
      Node ctnt =
          psb.tryStep(polarity ? ProofRule::TRUE_INTRO : ProofRule::FALSE_INTRO,
                      tiChildren,
                      {});
      if (ctnt.isNull() || ctnt.getKind() != Kind::EQUAL)
      {
        break;
      }
      std::vector<Node> tchildren;
      tchildren.push_back(ctnt);
      // apply substitution { contains(x,t) -> true|false } and rewrite to get
      // conclusion x = k1 ++ t ++ k2 or x != t.
      if (psb.applyPredTransform(res, conc, tchildren))
      {
        useBuffer = true;
      }
    }
    break;

    case InferenceId::STRINGS_REDUCTION:
    {
      size_t nchild = conc.getNumChildren();
      Node mainEq;
      if (conc.getKind() == Kind::EQUAL)
      {
        mainEq = conc;
      }
      else if (conc.getKind() == Kind::AND
               && conc[nchild - 1].getKind() == Kind::EQUAL)
      {
        mainEq = conc[nchild - 1];
      }
      if (mainEq.isNull())
      {
        Trace("strings-ipc-red") << "Bad Reduction: " << conc << std::endl;
        Assert(false) << "Unexpected reduction " << conc;
        break;
      }
      std::vector<Node> argsRed;
      // the left hand side of the last conjunct is the term we are reducing
      argsRed.push_back(mainEq[0]);
      Node red = psb.tryStep(ProofRule::STRING_REDUCTION, {}, argsRed);
      Trace("strings-ipc-red") << "Reduction : " << red << std::endl;
      if (!red.isNull())
      {
        // either equal or rewrites to it
        std::vector<Node> cexp;
        if (psb.applyPredTransform(red, conc, cexp))
        {
          Trace("strings-ipc-red") << "...success!" << std::endl;
          useBuffer = true;
        }
        else
        {
          Trace("strings-ipc-red") << "...failed to reduce" << std::endl;
        }
      }
    }
    break;
    // ========================== code injectivity
    case InferenceId::STRINGS_CODE_INJ:
    {
      ps.d_rule = ProofRule::STRING_CODE_INJ;
      Assert(conc.getKind() == Kind::OR && conc.getNumChildren() == 3
             && conc[2].getKind() == Kind::EQUAL);
      ps.d_args.push_back(conc[2][0]);
      ps.d_args.push_back(conc[2][1]);
    }
    break;
    // ========================== unit injectivity
    case InferenceId::STRINGS_UNIT_INJ:
    {
      ps.d_rule = ProofRule::STRING_SEQ_UNIT_INJ;
    }
    break;
    // ========================== prefix conflict
    case InferenceId::STRINGS_PREFIX_CONFLICT:
    case InferenceId::STRINGS_PREFIX_CONFLICT_MIN:
    {
      Trace("strings-ipc-prefix") << "Prefix conflict..." << std::endl;
      std::vector<Node> eqs;
      for (const Node& e : ps.d_children)
      {
        Kind ek = e.getKind();
        if (ek == Kind::EQUAL)
        {
          Trace("strings-ipc-prefix") << "- equality : " << e << std::endl;
          eqs.push_back(e);
        }
        else if (ek == Kind::STRING_IN_REGEXP)
        {
          // unfold it and extract the equality
          std::vector<Node> children;
          children.push_back(e);
          std::vector<Node> args;
          Node eunf = psb.tryStep(ProofRule::RE_UNFOLD_POS, children, args);
          Trace("strings-ipc-prefix")
              << "--- " << e << " unfolds to " << eunf << std::endl;
          if (eunf.isNull())
          {
            continue;
          }
          else if (eunf.getKind() == Kind::AND)
          {
            // equality is the first conjunct
            std::vector<Node> childrenAE;
            childrenAE.push_back(eunf);
            std::vector<Node> argsAE;
            argsAE.push_back(nm->mkConstInt(Rational(0)));
            Node eunfAE = psb.tryStep(ProofRule::AND_ELIM, childrenAE, argsAE);
            Trace("strings-ipc-prefix")
                << "--- and elim to " << eunfAE << std::endl;
            if (eunfAE.isNull() || eunfAE.getKind() != Kind::EQUAL)
            {
              Assert(false)
                  << "Unexpected unfolded premise " << eunf << " for " << infer;
              continue;
            }
            Trace("strings-ipc-prefix")
                << "- equality : " << eunfAE << std::endl;
            eqs.push_back(eunfAE);
          }
          else if (eunf.getKind() == Kind::EQUAL)
          {
            Trace("strings-ipc-prefix") << "- equality : " << eunf << std::endl;
            eqs.push_back(eunf);
          }
        }
        else
        {
          // not sure how to use this assumption
          Assert(false) << "Unexpected premise " << e << " for " << infer;
        }
      }
      if (eqs.empty())
      {
        break;
      }
      // connect via transitivity
      Node curr = eqs[0];
      std::vector<Node> subs;
      for (size_t i = 1, esize = eqs.size(); i < esize; i++)
      {
        Node prev = curr;
        curr = convertTrans(curr, eqs[i], psb);
        // if it is not a transitive step, it corresponds to a substitution
        if (curr.isNull())
        {
          curr = prev;
          // This is an equality between a variable and a concatention or
          // constant term (for example see below).
          // orient the substitution properly
          if (!eqs[i][1].isConst()
              && eqs[i][1].getKind() != Kind::STRING_CONCAT)
          {
            subs.push_back(eqs[i][1].eqNode(eqs[i][0]));
          }
          else
          {
            subs.push_back(eqs[i]);
          }
          continue;
        }
        Trace("strings-ipc-prefix") << "- Via trans: " << curr << std::endl;
      }
      if (curr.isNull())
      {
        break;
      }
      // Substitution is applied in reverse order
      // An example of this inference that uses a substituion is the conflict:
      //  (str.in_re w (re.++ (re.* re.allchar) (str.to_re "ABC")))
      //  (= w (str.++ z y x))
      //  (= x "D")
      // where we apply w -> (str.++ z y x), then x -> "D" to the first
      // predicate to obtain a conflict by rewriting (predicate elim).
      std::reverse(subs.begin(), subs.end());
      Trace("strings-ipc-prefix")
          << "- Possible conflicting equality : " << curr << std::endl;
      Node concE = psb.applyPredElim(curr,
                                     subs,
                                     MethodId::SB_DEFAULT,
                                     MethodId::SBA_SEQUENTIAL,
                                     MethodId::RW_EXT_REWRITE);
      Trace("strings-ipc-prefix")
          << "- After pred elim: " << concE << std::endl;
      if (concE == conc)
      {
        Trace("strings-ipc-prefix") << "...success!" << std::endl;
        useBuffer = true;
      }
    }
    break;
    // ========================== regular expressions
    case InferenceId::STRINGS_RE_INTER_INCLUDE:
    case InferenceId::STRINGS_RE_INTER_CONF:
    case InferenceId::STRINGS_RE_INTER_INFER:
    {
      std::vector<Node> reiExp;
      std::vector<Node> reis;
      std::vector<Node> reiChildren;
      std::vector<Node> reiChildrenOrig;
      Node x;
      // make the regular expression intersection that summarizes all
      // memberships in the explanation
      for (const Node& c : ps.d_children)
      {
        bool polarity = c.getKind() != Kind::NOT;
        Node catom = polarity ? c : c[0];
        if (catom.getKind() != Kind::STRING_IN_REGEXP)
        {
          Assert(c.getKind() == Kind::EQUAL);
          if (c.getKind() == Kind::EQUAL)
          {
            reiExp.push_back(c);
          }
          continue;
        }
        if (x.isNull())
        {
          // just take the first LHS; others should be equated to it by exp
          x = catom[0];
        }
        Node rcurr =
            polarity ? catom[1] : nm->mkNode(Kind::REGEXP_COMPLEMENT, catom[1]);
        reis.push_back(rcurr);
        Node mem = nm->mkNode(Kind::STRING_IN_REGEXP, catom[0], rcurr);
        reiChildren.push_back(mem);
        reiChildrenOrig.push_back(c);
      }
      // go back and justify each premise
      bool successChildren = true;
      for (size_t i = 0, nchild = reiChildren.size(); i < nchild; i++)
      {
        if (!psb.applyPredTransform(reiChildrenOrig[i], reiChildren[i], reiExp))
        {
          Trace("strings-ipc-re")
              << "... failed to justify child " << reiChildren[i] << " from "
              << reiChildrenOrig[i] << std::endl;
          successChildren = false;
          break;
        }
      }
      if (!successChildren)
      {
        break;
      }
      Node mem = psb.tryStep(ProofRule::RE_INTER, reiChildren, {});
      Trace("strings-ipc-re")
          << "Regular expression summary: " << mem << std::endl;
      // the conclusion is rewritable to the premises via rewriting?
      if (psb.applyPredTransform(mem, conc, {}))
      {
        Trace("strings-ipc-re") << "... success!" << std::endl;
        useBuffer = true;
      }
      else
      {
        Trace("strings-ipc-re")
            << "...failed to rewrite to conclusion" << std::endl;
      }
    }
    break;
    // ========================== unknown and currently unsupported
    case InferenceId::STRINGS_CARDINALITY:
    case InferenceId::STRINGS_I_CYCLE_E:
    case InferenceId::STRINGS_I_CYCLE:
    case InferenceId::STRINGS_INFER_EMP:
    case InferenceId::STRINGS_RE_DELTA:
    case InferenceId::STRINGS_RE_DELTA_CONF:
    case InferenceId::STRINGS_RE_DERIVE:
    case InferenceId::STRINGS_FLOOP:
    case InferenceId::STRINGS_FLOOP_CONFLICT:
    case InferenceId::STRINGS_DEQ_NORM_EMP:
    case InferenceId::STRINGS_CTN_TRANS:
    case InferenceId::STRINGS_CTN_DECOMPOSE:
    default:
      // do nothing, these will be converted to THEORY_INFERENCE below since the
      // rule is unknown.
      break;
  }

  // now see if we would succeed with the checker-to-try
  bool success = false;
  if (ps.d_rule != ProofRule::UNKNOWN)
  {
    Trace("strings-ipc") << "For " << infer << ", try proof rule " << ps.d_rule
                         << "...";
    Assert(ps.d_rule != ProofRule::UNKNOWN);
    Node pconc = psb.tryStep(ps.d_rule, ps.d_children, ps.d_args);
    if (pconc.isNull() || pconc != conc)
    {
      Trace("strings-ipc") << "failed, pconc is " << pconc << " (expected "
                           << conc << ")" << std::endl;
      ps.d_rule = ProofRule::UNKNOWN;
    }
    else
    {
      // successfully set up a single step proof in ps
      success = true;
      Trace("strings-ipc") << "success!" << std::endl;
    }
  }
  else if (useBuffer)
  {
    // successfully set up a multi step proof in psb
    success = true;
  }
  else
  {
    Trace("strings-ipc") << "For " << infer << " " << conc
                         << ", no proof rule, failed" << std::endl;
  }
  if (!success)
  {
    // debug print
    if (TraceIsOn("strings-ipc-fail"))
    {
      Trace("strings-ipc-fail")
          << "InferProofCons::convert: Failed " << infer
          << (isRev ? " :rev " : " ") << conc << std::endl;
      for (const Node& ec : exp)
      {
        Trace("strings-ipc-fail") << "    e: " << ec << std::endl;
      }
    }
    // untrustworthy conversion, the argument of THEORY_INFERENCE is its
    // conclusion
    ps.d_args.clear();
    ps.d_args.push_back(mkTrustId(TrustId::THEORY_INFERENCE));
    ps.d_args.push_back(conc);
    Node t = builtin::BuiltinProofRuleChecker::mkTheoryIdNode(THEORY_STRINGS);
    ps.d_args.push_back(t);
    // use the trust rule
    ps.d_rule = ProofRule::TRUST;
  }
  if (TraceIsOn("strings-ipc-debug"))
  {
    if (useBuffer)
    {
      Trace("strings-ipc-debug")
          << "InferProofCons::convert returned buffer with "
          << psb.getNumSteps() << " steps:" << std::endl;
      const std::vector<std::pair<Node, ProofStep>>& steps = psb.getSteps();
      for (const std::pair<Node, ProofStep>& step : steps)
      {
        Trace("strings-ipc-debug")
            << "- " << step.first << " via " << step.second << std::endl;
      }
    }
    else
    {
      Trace("strings-ipc-debug")
          << "InferProofCons::convert returned " << ps << std::endl;
    }
  }
}

bool InferProofCons::convertLengthPf(Node lenReq,
                                     const std::vector<Node>& lenExp,
                                     TheoryProofStepBuffer& psb)
{
  for (const Node& le : lenExp)
  {
    if (lenReq == le)
    {
      return true;
    }
  }
  Trace("strings-ipc-len") << "Must explain " << lenReq << " by " << lenExp
                           << std::endl;
  for (const Node& le : lenExp)
  {
    // probably rewrites to it?
    std::vector<Node> exp;
    if (psb.applyPredTransform(le, lenReq, exp))
    {
      Trace("strings-ipc-len") << "...success by rewrite" << std::endl;
      return true;
    }
    // maybe x != "" => len(x) != 0
    std::vector<Node> children;
    children.push_back(le);
    std::vector<Node> args;
    Node res = psb.tryStep(ProofRule::STRING_LENGTH_NON_EMPTY, children, args);
    if (res == lenReq)
    {
      Trace("strings-ipc-len") << "...success by LENGTH_NON_EMPTY" << std::endl;
      return true;
    }
  }
  Trace("strings-ipc-len") << "...failed" << std::endl;
  return false;
}

Node InferProofCons::convertTrans(Node eqa,
                                  Node eqb,
                                  TheoryProofStepBuffer& psb)
{
  if (eqa.getKind() != Kind::EQUAL || eqb.getKind() != Kind::EQUAL)
  {
    return Node::null();
  }
  for (uint32_t i = 0; i < 2; i++)
  {
    Node eqaSym = i == 0 ? eqa[1].eqNode(eqa[0]) : eqa;
    for (uint32_t j = 0; j < 2; j++)
    {
      Node eqbSym = j == 0 ? eqb : eqb[1].eqNode(eqb[0]);
      if (eqa[i] == eqb[j])
      {
        std::vector<Node> children;
        children.push_back(eqaSym);
        children.push_back(eqbSym);
        return psb.tryStep(ProofRule::TRANS, children, {});
      }
    }
  }
  return Node::null();
}

std::shared_ptr<ProofNode> InferProofCons::getProofFor(Node fact)
{
  // get the inference
  NodeInferInfoMap::iterator it = d_lazyFactMap.find(fact);
  if (it == d_lazyFactMap.end())
  {
    Node factSym = CDProof::getSymmFact(fact);
    if (!factSym.isNull())
    {
      // Use the symmetric fact. There is no need to explictly make a
      // SYMM proof, as this is handled by CDProof::getProofFor below.
      it = d_lazyFactMap.find(factSym);
    }
  }
  AlwaysAssert(it != d_lazyFactMap.end());
  std::shared_ptr<InferInfo> ii = (*it).second;
  Assert(ii->d_conc == fact);
  // make a placeholder proof using STRINGS_INFERENCE, which is reconstructed
  // during post-process
  CDProof pf(d_env);
  std::vector<Node> args;
  packArgs(ii->d_conc, ii->getId(), ii->d_idRev, ii->d_premises, args);
  // must flatten
  std::vector<Node> exp;
  for (const Node& ec : ii->d_premises)
  {
    utils::flattenOp(Kind::AND, ec, exp);
  }
  pf.addStep(fact, ProofRule::MACRO_STRING_INFERENCE, exp, args);
  return pf.getProofFor(fact);
}

std::string InferProofCons::identify() const
{
  return "strings::InferProofCons";
}

bool InferProofCons::purifyCoreSubstitutionAndTarget(
    PurifyType pt,
    Node& tgt,
    std::vector<Node>& children,
    TheoryProofStepBuffer& psb,
    bool concludeTgtNew)
{
  // collect the terms to purify, which are the LHS of the substitution
  std::unordered_set<Node> termsToPurify;
  if (!purifyCoreSubstitution(children, psb, termsToPurify))
  {
    return false;
  }
  // no need to purify, e.g. if all LHS of substitution are variables
  if (termsToPurify.empty())
  {
    return true;
  }
  // now, purify the target predicate
  tgt = purifyPredicate(pt, tgt, concludeTgtNew, psb, termsToPurify);
  if (tgt.isNull())
  {
    Trace("strings-ipc-pure-subs")
        << "...failed to purify target " << tgt << std::endl;
    return false;
  }
  return true;
}

bool InferProofCons::purifyCoreSubstitution(
    std::vector<Node>& children,
    TheoryProofStepBuffer& psb,
    std::unordered_set<Node>& termsToPurify)
{
  for (const Node& nc : children)
  {
    Assert(nc.getKind() == Kind::EQUAL);
    if (!nc[0].isVar())
    {
      termsToPurify.insert(nc[0]);
    }
  }
  // To avoid rare issues where purification variables introduced by this method
  // already appear in the inference, we also purify them here.
  SkolemManager* sm = NodeManager::currentNM()->getSkolemManager();
  SkolemId id;
  Node cval;
  for (const Node& nc : children)
  {
    // if this is a purification skolem of a term that is being purified,
    // we purify this.
    if (sm->isSkolemFunction(nc[0], id, cval) && id == SkolemId::PURIFY
        && termsToPurify.find(cval) != termsToPurify.end())
    {
      termsToPurify.insert(nc[0]);
    }
  }
  // now, purify each of the children of the substitution
  for (size_t i = 0, nchild = children.size(); i < nchild; i++)
  {
    Node pnc = purifyPredicate(
        PurifyType::SUBS_EQ, children[i], true, psb, termsToPurify);
    if (pnc.isNull())
    {
      Trace("strings-ipc-pure-subs")
          << "...failed to purify " << children[i] << std::endl;
      return false;
    }
    if (children[i] != pnc)
    {
      Trace("strings-ipc-pure-subs")
          << "Converted: " << children[i] << " to " << pnc << std::endl;
      children[i] = pnc;
    }
    // we now should have a substitution with only atomic terms
    Assert(children[i][0].getNumChildren() == 0);
  }
  return true;
}

Node InferProofCons::purifyPredicate(
    PurifyType pt,
    Node lit,
    bool concludeNew,
    TheoryProofStepBuffer& psb,
    const std::unordered_set<Node>& termsToPurify)
{
  bool pol = lit.getKind() != Kind::NOT;
  Node atom = pol ? lit : lit[0];
  NodeManager* nm = NodeManager::currentNM();
  Node newLit;
  if (pt == PurifyType::SUBS_EQ)
  {
    if (atom.getKind() != Kind::EQUAL)
    {
      Assert(false) << "Expected equality";
      return lit;
    }
    // purify the LHS directly, purify the RHS as a core term
    newLit = nm->mkNode(Kind::EQUAL,
                        maybePurifyTerm(atom[0], termsToPurify),
                        purifyCoreTerm(atom[1], termsToPurify));
  }
  else if (pt == PurifyType::CORE_EQ)
  {
    if (atom.getKind() != Kind::EQUAL || !atom[0].getType().isStringLike())
    {
      // we only purify string (dis)equalities
      return lit;
    }
    // purify both sides of the equality
    std::vector<Node> pcs;
    for (const Node& lc : atom)
    {
      pcs.push_back(purifyCoreTerm(lc, termsToPurify));
    }
    newLit = nm->mkNode(Kind::EQUAL, pcs);
  }
  else if (pt == PurifyType::EXTF)
  {
    if (atom.getKind() == Kind::EQUAL)
    {
      // purify the left hand side, which should be an extended function
      newLit =
          nm->mkNode(Kind::EQUAL, purifyApp(atom[0], termsToPurify), atom[1]);
    }
    else
    {
      // predicate case, e.g. for inferring contains
      newLit = purifyApp(atom, termsToPurify);
    }
  }
  else
  {
    Assert(false) << "Unknown purify type in InferProofCons::purifyPredicate";
  }
  if (!pol)
  {
    newLit = newLit.notNode();
  }
  if (lit == newLit)
  {
    // no change
    return lit;
  }
  // prove by transformation, should always succeed
  if (!psb.applyPredTransform(
          concludeNew ? lit : newLit, concludeNew ? newLit : lit, {}))
  {
    // failed, return null
    return Node::null();
  }
  return newLit;
}

Node InferProofCons::purifyCoreTerm(
    Node n, const std::unordered_set<Node>& termsToPurify)
{
  if (n.getKind() == Kind::STRING_CONCAT)
  {
    std::vector<Node> pcs;
    for (const Node& nc : n)
    {
      pcs.push_back(purifyCoreTerm(nc, termsToPurify));
    }
    return NodeManager::currentNM()->mkNode(Kind::STRING_CONCAT, pcs);
  }
  return maybePurifyTerm(n, termsToPurify);
}

Node InferProofCons::purifyApp(Node n,
                               const std::unordered_set<Node>& termsToPurify)
{
  if (n.getNumChildren() == 0)
  {
    return n;
  }
  std::vector<Node> pcs;
  for (const Node& nc : n)
  {
    pcs.push_back(maybePurifyTerm(nc, termsToPurify));
  }
  return NodeManager::currentNM()->mkNode(n.getKind(), pcs);
}

Node InferProofCons::maybePurifyTerm(
    Node n, const std::unordered_set<Node>& termsToPurify)
{
  if (termsToPurify.find(n) == termsToPurify.end())
  {
    // did not need to purify
    return n;
  }
  SkolemManager* sm = NodeManager::currentNM()->getSkolemManager();
  Node k = sm->mkPurifySkolem(n);
  return k;
}

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal
