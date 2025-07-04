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
 * Implementation of term database class.
 */

#include "theory/quantifiers/term_database.h"

#include "expr/skolem_manager.h"
#include "expr/sort_to_term.h"
#include "options/base_options.h"
#include "options/printer_options.h"
#include "options/quantifiers_options.h"
#include "options/smt_options.h"
#include "options/theory_options.h"
#include "options/uf_options.h"
#include "theory/quantifiers/ematching/trigger_term_info.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/quantifiers_inference_manager.h"
#include "theory/quantifiers/quantifiers_registry.h"
#include "theory/quantifiers/quantifiers_state.h"
#include "theory/quantifiers/term_util.h"
#include "theory/rewriter.h"
#include "theory/uf/equality_engine.h"

using namespace cvc5::internal::kind;
using namespace cvc5::context;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

TermDb::TermDb(Env& env, QuantifiersState& qs, QuantifiersRegistry& qr)
    : QuantifiersUtil(env),
      d_qstate(qs),
      d_qim(nullptr),
      d_qreg(qr),
      d_processed(context()),
      d_typeMap(context()),
      d_ops(context()),
      d_opMap(context()),
      d_inactive_map(context())
{
  d_true = nodeManager()->mkConst(true);
  d_false = nodeManager()->mkConst(false);
}

TermDb::~TermDb(){

}

void TermDb::finishInit(QuantifiersInferenceManager* qim)
{
  d_qim = qim;
}

void TermDb::registerQuantifier( Node q ) {
  Assert(q[0].getNumChildren() == d_qreg.getNumInstantiationConstants(q));
  for (size_t i = 0, nvars = q[0].getNumChildren(); i < nvars; i++)
  {
    Node ic = d_qreg.getInstantiationConstant(q, i);
    setTermInactive( ic );
  }
}

size_t TermDb::getNumOperators() const { return d_ops.size(); }

Node TermDb::getOperator(size_t i) const
{
  Assert(i < d_ops.size());
  return d_ops[i];
}

/** ground terms */
size_t TermDb::getNumGroundTerms(TNode f) const
{
  NodeDbListMap::const_iterator it = d_opMap.find(f);
  if (it != d_opMap.end())
  {
    return it->second->d_list.size();
  }
  return 0;
}

Node TermDb::getGroundTerm(TNode f, size_t i) const
{
  NodeDbListMap::const_iterator it = d_opMap.find(f);
  if (it != d_opMap.end())
  {
    Assert(i < it->second->d_list.size());
    return it->second->d_list[i];
  }
  Assert(false);
  return Node::null();
}

DbList* TermDb::getGroundTermList(TNode f) const
{
  NodeDbListMap::const_iterator it = d_opMap.find(f);
  if (it != d_opMap.end())
  {
    return it->second.get();
  }
  return nullptr;
}

size_t TermDb::getNumTypeGroundTerms(TypeNode tn) const
{
  TypeNodeDbListMap::const_iterator it = d_typeMap.find(tn);
  if (it != d_typeMap.end())
  {
    return it->second->d_list.size();
  }
  return 0;
}

Node TermDb::getTypeGroundTerm(TypeNode tn, size_t i) const
{
  TypeNodeDbListMap::const_iterator it = d_typeMap.find(tn);
  if (it != d_typeMap.end())
  {
    Assert(i < it->second->d_list.size());
    return it->second->d_list[i];
  }
  Assert(false);
  return Node::null();
}

Node TermDb::getOrMakeTypeGroundTerm(TypeNode tn, bool reqVar)
{
  TypeNodeDbListMap::const_iterator it = d_typeMap.find(tn);
  if (it != d_typeMap.end())
  {
    Assert(!it->second->d_list.empty());
    if (!reqVar)
    {
      return it->second->d_list[0];
    }
    for (const Node& v : it->second->d_list)
    {
      if (v.isVar())
      {
        return v;
      }
    }
  }
  return getOrMakeTypeFreshVariable(tn);
}

Node TermDb::getOrMakeTypeFreshVariable(TypeNode tn)
{
  std::unordered_map<TypeNode, Node>::iterator it = d_type_fv.find(tn);
  if (it == d_type_fv.end())
  {
    NodeManager* nm = nodeManager();
    SkolemManager* sm = nm->getSkolemManager();
    std::vector<Node> cacheVals;
    cacheVals.push_back(nm->mkConst(SortToTerm(tn)));
    Node k = sm->mkSkolemFunction(SkolemId::GROUND_TERM, cacheVals);
    Trace("mkVar") << "TermDb:: Make variable " << k << " : " << tn
                   << std::endl;
    if (options().quantifiers.instMaxLevel != -1)
    {
      QuantAttributes::setInstantiationLevelAttr(k, 0);
    }
    d_type_fv[tn] = k;
    return k;
  }
  return it->second;
}

Node TermDb::getMatchOperator(TNode n)
{
  Kind k = n.getKind();
  //datatype operators may be parametric, always assume they are
  if (k == Kind::SELECT || k == Kind::STORE || k == Kind::SET_UNION
      || k == Kind::SET_INTER || k == Kind::SET_SUBSET || k == Kind::SET_MINUS
      || k == Kind::SET_MEMBER || k == Kind::SET_SINGLETON
      || k == Kind::APPLY_SELECTOR || k == Kind::APPLY_TESTER
      || k == Kind::SEP_PTO || k == Kind::HO_APPLY || k == Kind::SEQ_NTH
      || k == Kind::STRING_LENGTH || k == Kind::BITVECTOR_TO_NAT
      || k == Kind::INT_TO_BITVECTOR)
  {
    //since it is parametric, use a particular one as op
    TypeNode tn = n[0].getType();
    Node op = n.getOperator();
    std::map< Node, std::map< TypeNode, Node > >::iterator ito = d_par_op_map.find( op );
    if( ito!=d_par_op_map.end() ){
      std::map< TypeNode, Node >::iterator it = ito->second.find( tn );
      if( it!=ito->second.end() ){
        return it->second;
      }
    }
    Trace("par-op") << "Parametric operator : " << k << ", " << n.getOperator() << ", " << tn << " : " << n << std::endl;
    d_par_op_map[op][tn] = n;
    return n;
  }
  else if (inst::TriggerTermInfo::isAtomicTriggerKind(k))
  {
    return n.getOperator();
  }
  return Node::null();
}

bool TermDb::isMatchable(TNode n) { return !getMatchOperator(n).isNull(); }

void TermDb::addTerm(Node n)
{
  if (d_processed.find(n) != d_processed.end())
  {
    return;
  }
  d_processed.insert(n);
  if (!TermUtil::hasInstConstAttr(n))
  {
    Trace("term-db-debug") << "register term : " << n << std::endl;
    DbList* dlt = getOrMkDbListForType(n.getType());
    dlt->d_list.push_back(n);
    // if this is an atomic trigger, consider adding it
    Node op = getMatchOperator(n);
    if (!op.isNull())
    {
      Trace("term-db") << "register term in db " << n << std::endl;
      Trace("term-db-debug") << "  match operator is : " << op << std::endl;
      DbList* dlo = getOrMkDbListForOp(op);
      dlo->d_list.push_back(n);
      // If we are higher-order, we may need to register more terms.
      addTermInternal(n);
    }
  }
  else
  {
    setTermInactive(n);
  }
  if (!n.isClosure())
  {
    for (const Node& nc : n)
    {
      addTerm(nc);
    }
  }
}

DbList* TermDb::getOrMkDbListForType(TypeNode tn)
{
  TypeNodeDbListMap::iterator it = d_typeMap.find(tn);
  if (it != d_typeMap.end())
  {
    return it->second.get();
  }
  std::shared_ptr<DbList> dl = std::make_shared<DbList>(context());
  d_typeMap.insert(tn, dl);
  return dl.get();
}

DbList* TermDb::getOrMkDbListForOp(TNode op)
{
  NodeDbListMap::iterator it = d_opMap.find(op);
  if (it != d_opMap.end())
  {
    return it->second.get();
  }
  std::shared_ptr<DbList> dl = std::make_shared<DbList>(context());
  d_opMap.insert(op, dl);
  Assert(op.getKind() != Kind::BOUND_VARIABLE);
  d_ops.push_back(op);
  return dl.get();
}

void TermDb::computeArgReps( TNode n ) {
  if (d_arg_reps.find(n) == d_arg_reps.end())
  {
    eq::EqualityEngine* ee = d_qstate.getEqualityEngine();
    std::vector<TNode>& tars = d_arg_reps[n];
    for (const TNode& nc : n)
    {
      TNode r = ee->hasTerm(nc) ? ee->getRepresentative(nc) : nc;
      tars.emplace_back(r);
    }
  }
}

void TermDb::computeUfEqcTerms( TNode f ) {
  Assert(f == getOperatorRepresentative(f));
  if (d_func_map_eqc_trie.find(f) != d_func_map_eqc_trie.end())
  {
    return;
  }
  TNodeTrie& tnt = d_func_map_eqc_trie[f];
  tnt.clear();
  // get the matchable operators in the equivalence class of f
  std::vector<TNode> ops;
  getOperatorsFor(f, ops);
  eq::EqualityEngine* ee = d_qstate.getEqualityEngine();
  for (TNode ff : ops)
  {
    DbList* dbl = getOrMkDbListForOp(ff);
    for (const Node& n : dbl->d_list)
    {
      if (hasTermCurrent(n) && isTermActive(n))
      {
        computeArgReps(n);
        TNode r = ee->hasTerm(n) ? ee->getRepresentative(n) : TNode(n);
        tnt.d_data[r].addTerm(n, d_arg_reps[n]);
      }
    }
  }
}

void TermDb::computeUfTerms( TNode f ) {
  if (d_op_nonred_count.find(f) != d_op_nonred_count.end())
  {
    // already computed
    return;
  }
  Assert(f == getOperatorRepresentative(f));
  d_op_nonred_count[f] = 0;
  // get the matchable operators in the equivalence class of f
  std::vector<TNode> ops;
  getOperatorsFor(f, ops);
  Trace("term-db-debug") << "computeUfTerms for " << f << std::endl;
  unsigned congruentCount = 0;
  unsigned nonCongruentCount = 0;
  unsigned alreadyCongruentCount = 0;
  unsigned relevantCount = 0;
  NodeManager* nm = nodeManager();
  for (TNode ff : ops)
  {
    NodeDbListMap::iterator it = d_opMap.find(ff);
    if (it == d_opMap.end())
    {
      // no terms for this operator
      continue;
    }
    Trace("term-db-debug") << "Adding terms for operator " << ff << std::endl;
    for (const Node& n : it->second->d_list)
    {
      // to be added to term index, term must be relevant, and exist in EE
      if (!hasTermCurrent(n) || !d_qstate.hasTerm(n))
      {
        Trace("term-db-debug") << n << " is not relevant." << std::endl;
        continue;
      }

      relevantCount++;
      if (!isTermActive(n))
      {
        Trace("term-db-debug") << n << " is already redundant." << std::endl;
        alreadyCongruentCount++;
        continue;
      }

      computeArgReps(n);
      std::vector<TNode>& reps = d_arg_reps[n];
      Trace("term-db-debug") << "Adding term " << n << " with arg reps : ";
      std::vector<std::vector<TNode> >& frds = d_fmapRelDom[f];
      size_t rsize = reps.size();
      // ensure the relevant domain vector has been allocated
      frds.resize(rsize);
      for (size_t i = 0; i < rsize; i++)
      {
        TNode r = reps[i];
        Trace("term-db-debug") << r << " ";
        std::vector<TNode>& frd = frds[i];
        if (std::find(frd.begin(), frd.end(), r) == frd.end())
        {
          frd.push_back(r);
        }
      }
      Trace("term-db-debug") << std::endl;
      Assert(d_qstate.hasTerm(n));
      Trace("term-db-debug")
          << "  and value : " << d_qstate.getRepresentative(n) << std::endl;
      Node at = d_func_map_trie[f].addOrGetTerm(n, reps);
      Assert(d_qstate.hasTerm(at));
      Trace("term-db-debug2") << "...add term returned " << at << std::endl;
      if (at != n && d_qstate.areEqual(at, n))
      {
        setTermInactive(n);
        Trace("term-db-debug") << n << " is redundant." << std::endl;
        congruentCount++;
        continue;
      }
      std::vector<Node> lits;
      if (checkCongruentDisequal(at, n, lits))
      {
        Assert(at.getNumChildren() == n.getNumChildren());
        for (size_t k = 0, size = at.getNumChildren(); k < size; k++)
        {
          if (at[k] != n[k])
          {
            lits.push_back(nm->mkNode(Kind::EQUAL, at[k], n[k]).negate());
            Assert(d_qstate.areEqual(at[k], n[k]));
          }
        }
        Node lem = nm->mkOr(lits);
        if (TraceIsOn("term-db-lemma"))
        {
          Trace("term-db-lemma") << "Disequal congruent terms : " << at << " "
                                 << n << "!!!!" << std::endl;
          if (!d_qstate.getValuation().needCheck())
          {
            Trace("term-db-lemma")
                << "  all theories passed with no lemmas." << std::endl;
            // we should be a full effort check, prior to theory combination
          }
          Trace("term-db-lemma") << "  add lemma : " << lem << std::endl;
        }
        d_qim->addPendingLemma(lem, InferenceId::QUANTIFIERS_TDB_DEQ_CONG);
        d_qstate.notifyInConflict();
        return;
      }
      nonCongruentCount++;
      d_op_nonred_count[f]++;
    }
    if (TraceIsOn("tdb"))
    {
      Trace("tdb") << "Term db size [" << f << "] : " << nonCongruentCount
                   << " / ";
      Trace("tdb") << (nonCongruentCount + congruentCount) << " / "
                   << (nonCongruentCount + congruentCount
                       + alreadyCongruentCount)
                   << " / ";
      Trace("tdb") << relevantCount << " / " << it->second->d_list.size()
                   << std::endl;
    }
  }
}

Node TermDb::getOperatorRepresentative(TNode op) const { return op; }

bool TermDb::checkCongruentDisequal(TNode a, TNode b, std::vector<Node>& exp)
{
  if (d_qstate.areDisequal(a, b))
  {
    exp.push_back(a.eqNode(b));
    return true;
  }
  return false;
}

bool TermDb::inRelevantDomain(TNode f, size_t i, TNode r)
{
  // notice if we are not higher-order, getOperatorRepresentative is a no-op
  f = getOperatorRepresentative(f);
  computeUfTerms(f);
  Assert(!d_qstate.getEqualityEngine()->hasTerm(r)
         || d_qstate.getEqualityEngine()->getRepresentative(r) == r);
  std::map<Node, std::vector<std::vector<TNode> > >::const_iterator it =
      d_fmapRelDom.find(f);
  if (it != d_fmapRelDom.end())
  {
    Assert(i < it->second.size());
    const std::vector<TNode>& rd = it->second[i];
    return std::find(rd.begin(), rd.end(), r) != rd.end();
  }
  return false;
}

bool TermDb::isTermActive(Node n)
{
  return d_inactive_map.find( n )==d_inactive_map.end(); 
  //return !n.getAttribute(NoMatchAttribute());
}

void TermDb::setTermInactive(Node n) { d_inactive_map[n] = true; }

bool TermDb::hasTermCurrent(const Node& n, bool useMode) const
{
  if( !useMode ){
    return d_has_map.find( n )!=d_has_map.end();
  }
  //some assertions are not sent to EE
  if (options().quantifiers.termDbMode == options::TermDbMode::ALL)
  {
    return true;
  }
  else if (options().quantifiers.termDbMode == options::TermDbMode::RELEVANT)
  {
    return d_has_map.find( n )!=d_has_map.end();
  }
  Assert(false) << "TermDb::hasTermCurrent: Unknown termDbMode : "
                << options().quantifiers.termDbMode;
  return false;
}

bool TermDb::isTermEligibleForInstantiation(TNode n, TNode f)
{
  if (options().quantifiers.instMaxLevel != -1)
  {
    uint64_t level;
    if (QuantAttributes::getInstantiationLevel(n, level))
    {
      int64_t fml =
          f.isNull() ? -1 : d_qreg.getQuantAttributes().getQuantInstLevel(f);
      unsigned ml = fml >= 0 ? fml : options().quantifiers.instMaxLevel;

      if (level > ml)
      {
        Trace("inst-add-debug")
            << "Term " << n << " has instantiation level " << level;
        Trace("inst-add-debug") << ", which is more than maximum allowed level " << ml << " for this quantified formula." << std::endl;
        return false;
      }
    }
    else
    {
      Trace("inst-add-debug")
          << "Term " << n << " does not have an instantiation level."
          << std::endl;
      return false;
    }
  }
  // it cannot have instantiation constants, which originate from
  // counterexample-guided instantiation strategies.
  return !TermUtil::hasInstConstAttr(n);
}

Node TermDb::getEligibleTermInEqc( TNode r ) {
  if( isTermEligibleForInstantiation( r, TNode::null() ) ){
    return r;
  }else{
    std::map< Node, Node >::iterator it = d_term_elig_eqc.find( r );
    if( it==d_term_elig_eqc.end() ){
      Node h;
      eq::EqualityEngine* ee = d_qstate.getEqualityEngine();
      eq::EqClassIterator eqc_i = eq::EqClassIterator(r, ee);
      while (!eqc_i.isFinished())
      {
        TNode n = (*eqc_i);
        ++eqc_i;
        if (isTermEligibleForInstantiation(n, TNode::null()))
        {
          h = n;
          break;
        }
      }
      d_term_elig_eqc[r] = h;
      return h;
    }else{
      return it->second;
    }
  }
}

bool TermDb::finishResetInternal(Theory::Effort e)
{
  // do nothing
  return true;
}

void TermDb::addTermInternal(Node n)
{
  // do nothing
}

void TermDb::getOperatorsFor(TNode f, std::vector<TNode>& ops)
{
  ops.push_back(f);
}

void TermDb::setHasTerm( Node n ) {
  Trace("term-db-debug2") << "hasTerm : " << n  << std::endl;
  if( d_has_map.find( n )==d_has_map.end() ){
    d_has_map[n] = true;
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      setHasTerm( n[i] );
    }
  }
}

void TermDb::presolve() {}

bool TermDb::reset( Theory::Effort effort ){
  d_op_nonred_count.clear();
  d_arg_reps.clear();
  d_func_map_trie.clear();
  d_func_map_eqc_trie.clear();
  d_fmapRelDom.clear();

  eq::EqualityEngine* ee = d_qstate.getEqualityEngine();

  Assert(ee->consistent());

  //compute has map
  if (options().quantifiers.termDbMode == options::TermDbMode::RELEVANT)
  {
    d_has_map.clear();
    d_term_elig_eqc.clear();
    eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( ee );
    while( !eqcs_i.isFinished() ){
      TNode r = (*eqcs_i);
      bool addedFirst = false;
      Node first;
      //TODO: ignoring singleton eqc isn't enough, need to ensure eqc are relevant
      eq::EqClassIterator eqc_i = eq::EqClassIterator(r, ee);
      while( !eqc_i.isFinished() ){
        TNode n = (*eqc_i);
        if( first.isNull() ){
          first = n;
        }else{
          if( !addedFirst ){
            addedFirst = true;
            setHasTerm( first );
          }
          setHasTerm( n );
        }
        ++eqc_i;
      }
      ++eqcs_i;
    }
    const LogicInfo& logicInfo = d_qstate.getLogicInfo();
    for (TheoryId theoryId = THEORY_FIRST; theoryId < THEORY_LAST; ++theoryId)
    {
      if (!logicInfo.isTheoryEnabled(theoryId))
      {
        continue;
      }
      for (context::CDList<Assertion>::const_iterator
               it = d_qstate.factsBegin(theoryId),
               it_end = d_qstate.factsEnd(theoryId);
           it != it_end;
           ++it)
      {
        setHasTerm((*it).d_assertion);
      }
    }
  }
  // finish reset
  return finishResetInternal(effort);
}

TNodeTrie* TermDb::getTermArgTrie(Node f)
{
  f = getOperatorRepresentative(f);
  computeUfTerms( f );
  std::map<Node, TNodeTrie>::iterator itut = d_func_map_trie.find(f);
  if( itut!=d_func_map_trie.end() ){
    return &itut->second;
  }else{
    return NULL;
  }
}

TNodeTrie* TermDb::getTermArgTrie(Node eqc, Node f)
{
  f = getOperatorRepresentative(f);
  computeUfEqcTerms( f );
  std::map<Node, TNodeTrie>::iterator itut = d_func_map_eqc_trie.find(f);
  if( itut==d_func_map_eqc_trie.end() ){
    return NULL;
  }else{
    if( eqc.isNull() ){
      return &itut->second;
    }else{
      std::map<TNode, TNodeTrie>::iterator itute =
          itut->second.d_data.find(eqc);
      if( itute!=itut->second.d_data.end() ){
        return &itute->second;
      }else{
        return NULL;
      }
    }
  }
}

TNode TermDb::getCongruentTerm( Node f, Node n ) {
  f = getOperatorRepresentative(f);
  computeUfTerms( f );
  std::map<Node, TNodeTrie>::iterator itut = d_func_map_trie.find(f);
  if( itut!=d_func_map_trie.end() ){
    computeArgReps( n );
    return itut->second.existsTerm( d_arg_reps[n] );
  }
  return TNode::null();
}

TNode TermDb::getCongruentTerm(Node f, const std::vector<TNode>& args)
{
  f = getOperatorRepresentative(f);
  computeUfTerms( f );
  return d_func_map_trie[f].existsTerm( args );
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
