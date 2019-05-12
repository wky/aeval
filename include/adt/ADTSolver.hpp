#ifndef ADTSOLVER__HPP__
#define ADTSOLVER__HPP__
#include <assert.h>
#include <string.h>
#include <chrono>
#include <iterator>
#include <unistd.h>
#include "ae/SMTUtils.hpp"
#include "ufo/Smt/EZ3.hh"
#include <getopt.h>
#include <algorithm>

#include <iostream>

#define LOG(_level, _code) \
  do{ if (_level <= _global_verbosity) _code; \
  } while(0)

using namespace std;
namespace ufo
{


  typedef std::multimap<Expr,Expr> ExprMMap;

  bool find_expr_mmap(ExprMMap& mp, Expr ty, Expr e){
    auto range = mp.equal_range(ty);
    for (auto iter = range.first; iter != range.second; ++iter)
      if (iter->second == e) return true;
    return false;
  }

  static int _global_verbosity = 1;
  struct Config {
    int flipIH = 0;
    int genFapp = 0;
    int tryAssoc = 0;
    int tryComm = 0;
    int moreFail = 0;
    int lemmaTmpl = 1;
    int maxSearchD = 15;
    int maxSameAssm = 5;
    int maxTermDepth = 3;
    int noCtor = 0;
    int refuteTests = 3;
    int refuteSimpl = 35;
    int timeoutSecs = 10;
    int tryCandidates = 5;
    int presolveTimes = 8;

    Config(int argc, char** argv) {
      static struct option long_options[] = {
        {"flip-ih", no_argument, NULL,  'F'},
        {"gen-fapp", required_argument, NULL, 'G'},
        {"try-assoc", no_argument, NULL, 'A'},
        {"try-comm", no_argument, NULL, 'c'},
        {"more-fail", no_argument, NULL, 'f'},
        {"template", required_argument,  NULL,  'T'},
        {"max-search",  required_argument, NULL, 'D'},
        {"max-same-assm", required_argument, NULL, 'S'},
        {"term-depth", required_argument, NULL, 'd'},
        {"no-ctor", no_argument, NULL, 'N'},
        {"refute-test", required_argument, NULL, 'R'},
        {"refute-simpl", required_argument, NULL, 's'},
        {"timeout", required_argument, NULL, 'O'},
        {"candidates", required_argument, NULL, 'C'},
        {"preprocess", required_argument, NULL, 'P'},
        {"verbose", required_argument,  NULL,  'V'},
        {0,         0,                 0,  0 }
      };
      int c;
      while(1) {
        int opt_idx;
        c = getopt_long(argc, argv, "FT:D:S:d:R:s:O:C:P:V:", long_options, &opt_idx);
        if (c == -1) break;
        int value = -1;
        if (optarg) value = atoi(optarg);
        switch(c){
          case 0: break;
        
          case 'F':
            flipIH = 1;
            break;
          case 'G':
            genFapp = value;
            break;
          case 'A':
            tryAssoc = 1;
            break;
          case 'c':
            tryComm = 1;
            break;
          case 'f':
            moreFail = 1;
          case 'T':
            lemmaTmpl = value;
            break;

          case 'D':
            maxSearchD = value;
            break;

          case 'S':
            maxSameAssm = value;
            break;

          case 'd':
            maxTermDepth = value;
            break;

          case 'N':
            noCtor = 1;
            break;

          case 'R':
            refuteTests = value;
            break;

          case 's':
            refuteSimpl = value;
            break;

          case 'O':
            timeoutSecs = value;
            break;

          case 'C':
            tryCandidates = value;
            break;

          case 'P':
            presolveTimes = value;
            break;
          
          case 'V':
            _global_verbosity = value;
            break;

          case '?':
            break;

          default:
            assert(0 && "bad arg");
        }
      }

    }
  };

  struct SimplifyAdd0
  { 
    Expr operator()(Expr e) const{
      bind::IsHardIntConst isInt;
      if (!isOpX<PLUS>(e) || e->arity() != 2) return NULL;
      if (isInt(e->left()) && getTerm<mpz_class>(e->left()) == 0)
        return e->right();
      if (isInt(e->right()) && getTerm<mpz_class>(e->right()) == 0)
        return e->left();
      else return NULL;
    }
  };

  Expr makeAddExpr(ExprVector ev){
    if (ev.size()>1) return mknary<PLUS>(ev);
    else if (ev.size() == 1) return ev[0];
    else return NULL;
  }
  Expr simplifyAdd(Expr e){
    if (!(isOpX<EQ>(e) && isOpX<PLUS>(e->left()) && isOpX<PLUS>(e->right()))) return e;
    bind::IsHardIntConst isInt;
    mpz_class lhsConst = 0;
    mpz_class rhsConst = 0;
    ExprVector lhsInts;
    ExprVector rhsInts;
    for (Expr lhsArg : boost::make_iterator_range(e->left()->args_begin (), e->left()->args_end ()))
      if (isInt(lhsArg))
        lhsConst += getTerm<mpz_class>(lhsArg);
      else lhsInts.push_back(lhsArg);
    for (Expr rhsArg : boost::make_iterator_range(e->right()->args_begin (), e->right()->args_end()))
      if (isInt(rhsArg))
        rhsConst += getTerm<mpz_class>(rhsArg);
      else rhsInts.push_back(rhsArg);

    if (lhsConst != rhsConst)
      lhsInts.push_back(mkTerm<mpz_class>(lhsConst - rhsConst, e->efac()));
    return mk<EQ>(makeAddExpr(lhsInts), makeAddExpr(rhsInts));
  }
  class TermEnumerator
  {
  private:
    ExprMMap baseCtors;
    ExprMMap indCtors;
    ExprSet vars;
    ExprSet funcs;
    int maxDepth;
    bool noCtor;
    vector<size_t> depthIdx;
    bool isVarFn(Expr e){
      if (isOpX<FAPP> (e) && e->arity () == 1 && isOpX<FDECL> (e->first())) {
        return !(find_expr_mmap(baseCtors, bind::typeOf(e), bind::fname(e)));
      } else return false;
    }
    bool isBaseCtor(Expr e){
      return (isOpX<FAPP> (e) && e->arity () == 1 && isOpX<FDECL> (e->first()) 
        && find_expr_mmap(baseCtors, bind::typeOf(e), bind::fname(e)));
    }
    bool isFuncFn(Expr e){
      // fdecl [name fromTy ... toTy]
      if (isOpX<FDECL> (e) && e->arity () >= 3) {
        return true;
      } else return false;
    }
    // bool isIndCtorFn(Expr e){
    //   if (isOpX<FAPP> (e) && isOpX<FDECL> (e->first())){
    //     if (find(indCtorDecls.begin(), indCtorDecls.end(), e->first()) != indCtorDecls.end())
    //       return true;
    //   }
    //   return false;
    // }
  public:
    map<Expr, ExprVector> allTerms;
    TermEnumerator(Expr expr, ExprMMap _baseCtors, ExprMMap _indCtors, int _maxDepth = 3, bool _noCtor = false) :
      baseCtors(_baseCtors), indCtors(_indCtors), maxDepth(_maxDepth), noCtor(_noCtor)
    {
      LOG(1, outs()<<"<term-enum> from expr: "<<*expr<<"\n");
      filter(expr, [this](Expr e){return isVarFn(e);}, inserter(vars, vars.end()));
      filter(expr, [this](Expr e){return isFuncFn(e);}, inserter(funcs, funcs.end()));

      if (!noCtor){
      for(auto p: indCtors)
      {
        if (p.second)
          funcs.insert(p.second);
      }}
    }
    void addFunctions(Expr axiom){
      filter(axiom, [this](Expr e){return isFuncFn(e);}, inserter(funcs, funcs.end()));
    }

    int depth(Expr e)
    {
      bind::IsConst isConst;
      int maxD = 0;
      if (isConst(e)) return 1;
      if (isOpX<FAPP>(e))
      {
        for (int i = 0; i < bind::domainSz(e->first()); i++)
        {
          int d = depth(e->arg(i+1));
          if (d > maxD) maxD = d;
        }
      }
      return maxD + 1;
    }
    void getTerms()
    {
      LOG(5, outs()<<"<term-enum> base terms:\n");
      for (Expr v: vars)
      {
        allTerms[bind::typeOf(v)].push_back(v);
        LOG(5, outs()<<"Variable "<<*v<<" of type: "<<*bind::typeOf(v)<<"\n");
      }
      if (!noCtor){
      for (auto p: baseCtors)
      {
        if (!p.second || (p.second)->arity() != 2) continue;
        allTerms[p.first].push_back(bind::fapp(p.second));
        LOG(5, outs()<<"Ctor "<<*bind::fapp(p.second)<<" of type: "<<*(p.first)<<"\n");
      }}

      LOG(5, for (Expr f: funcs) outs()<<"Function "<<*f);
      LOG(5, outs()<<"\n");

      int i, d;
      for (d = 1; d < maxDepth; d++)
      {
        ExprVector newTerms;
        for (Expr fdecl : funcs)
        {
          Expr ty = fdecl->last();
          int nArgs = bind::domainSz(fdecl);
          ExprVector conArgs(nArgs, NULL); // concrete args
          // check required type terms exist
          bool termsExist = true;
          for (i = 0; i < nArgs; i++)
            if (allTerms.count(bind::domainTy(fdecl, i)) == 0){
              termsExist = false;
              break;
            }
          // chose another function
          if (!termsExist) continue;

          // stack
          vector<int> stk(nArgs, 0);
          while (true)
          {
            bool allBaseCtor = true;
            for (i = 0; i < nArgs; i++)
            {
              int choice = stk[i];
              conArgs[i] = allTerms[bind::domainTy(fdecl, i)][choice];
              if (!isBaseCtor(conArgs[i])) allBaseCtor = false;
            }
            // ok to have len(nil) and such
            if (nArgs == 1) allBaseCtor = false;

            Expr term = bind::fapp(fdecl, conArgs);
            if (depth(term) == d+1 && !allBaseCtor) // at least d+1, not OK to have (append nil nil)
              newTerms.push_back(term);

            for (i = 0; i < nArgs; i++)
            {
              stk[i] ++;
              if (stk[i] < allTerms[bind::domainTy(fdecl, i)].size()) break;
              else stk[i] = 0;
            }
            if (i == nArgs) break;
          }
        }
        LOG(5, outs()<<"<term-enum> Depth "<<d<<" terms ("<<newTerms.size()<<"):\n");
        for (Expr t : newTerms)
        {
          // TODO check depth
          Expr ty = bind::typeOf(t);
          allTerms[ty].push_back(t);
          LOG(5, outs()<<" => "<<*t<<" of type: "<<*ty<<"\n");
        }
      }
    }

    ~TermEnumerator(){}
    
  };
  class ADTSolver
  {
    private:
    static int _cntr;
    static bool _triedAssoc;
    static bool _triedComm;
    Expr goal;
    // assumptions should be copied, prevents changes propagating
    ExprVector assumptions;
    ExprVector constructors;

    ExprMMap baseConstructors;
    ExprMMap indConstructors;

    ExprFactory &efac;
    SMTUtils u;

    ExprVector rewriteHistory;
    vector<int> rewriteSequence;
    ExprSet rewriteSet;
    Config cfg;
    
    bool baseOrInd;

    int maxDepthCnt;
    int failureCnt;
    int btCnt;

    ExprSet failures;

    ExprSet indCtorDecls;
    ExprMap valueMap;

    ExprVector newLemmas;


    int _nextInt;
    std::chrono::duration<int> maxTime;
    std::chrono::system_clock::time_point begin;

    int branches;
    int nodes;
    bool importedFailure;
    public:

    ADTSolver(Expr _goal, ExprVector& _assumptions, ExprVector& _constructors, Config _cfg) :
        goal(_goal), assumptions(_assumptions), constructors(_constructors),
        efac(_goal->getFactory()), u(_goal->getFactory()), cfg(_cfg), maxTime(cfg.timeoutSecs)
    {
      assert(isOpX<FORALL>(goal));
      // new instance of ADTSolver
      _cntr ++;
      _nextInt = 0;
      importedFailure = false;
    }
    void saveBranchFactor(int b){
      branches += b;
      nodes ++;
    }
    bool simplifyGoal(Expr& g)
    {
      Expr goalQF = g->last();
      for (auto & a : assumptions)
      {
        Expr goalSimpl = useAssumption(goalQF, a);
        if (goalSimpl != NULL) goalQF = goalSimpl;
      }
      goalQF = liftITEs(goalQF); // TODO: more simplification passes
      goalQF = u.simplifyITE(goalQF);
      if (u.isEquiv(goalQF, mk<TRUE>(efac))) return true;

      ExprVector args;
      for (int i = 0; i < g->arity() - 1; i++)
      {
        if (contains(g->last(), g->arg(i))) args.push_back(g->arg(i));
      }
      if (args.size() == 0) g = goalQF;
      else
      {
        args.push_back(goalQF);
        g = mknary<FORALL>(args);
      }
      rewriteHistory.push_back(g);
      return false;
    }
    bool testNotEQ(Expr eq){
      if (!isOpX<EQ>(eq)) return false;
      Expr lhs = eq->first();
      Expr rhs = eq->last();
      ExprVector lF, rF;
      auto isF = [](Expr e){return isOpX<FDECL> (e) && e->arity () >= 3;}; 
      filter(lhs, isF, back_inserter(lF));
      filter(rhs, isF, back_inserter(rF));
      bool lSimple = true, rSimple = true;
      for (Expr f: lF) if (find(indCtorDecls.begin(), indCtorDecls.end(), f) == indCtorDecls.end()) { lSimple = false; break;}
      for (Expr f: rF) if (find(indCtorDecls.begin(), indCtorDecls.end(), f) == indCtorDecls.end()) { rSimple = false; break;}
      if (lSimple && rSimple) return lhs != rhs;
      // else if (lSimple != rSimple) return true;
      else return false;
    }
    bool refuteGoal(Expr goalQF, int nTimes)
    {
      for (int i = 0; i < nTimes; ++i)
      {
        for (auto & a : assumptions) {
          Expr goalSimpl = useAssumption(goalQF, a);
          if (goalSimpl != NULL) goalQF = goalSimpl;
        }
      }
      // if (u.isEquiv(goalQF, mk<FALSE>(efac))){
      if (u.isFalse(goalQF) || testNotEQ(goalQF)){
        LOG(2, outs()<<" *** REFUTED!!!: "<<*goalQF<<"\n");
        return false;
      } 
      if (u.isTrue(goalQF)){
        LOG(4, outs()<<" *** Valid!!!\n");
        return true;
      }
      return true;
    }

    // main method to do rewriting
    Expr useAssumption(Expr subgoal, Expr assm)
    {
      subgoal = liftITEs(subgoal);
      if (isOpX<FORALL>(assm))
      {
        ExprMap matching;
        ExprVector args;
        for (int i = 0; i < assm->arity() - 1; i++) args.push_back(bind::fapp(assm->arg(i)));
        Expr assmQF = assm->last();
        Expr repl = assmQF;

        // we first search for a matching of the entire assumption (usually some inequality)
        if (findMatchingSubexpr (assmQF, subgoal, args, matching))
        {
          for (auto & a : matching) repl = replaceAll(repl, a.first, a.second);
          Expr replaced = replaceAll(subgoal, repl, mk<TRUE>(efac));
          if (subgoal != replaced) return replaced;
        }
        if (isOpX<EQ>(assmQF))
        {
          matching.clear();

          // if the assumption is equality, the we search for a matching of its LHS
          // (we can try matching the RHS as well, but it will likely give us infinite loops)
          if (findMatchingSubexpr (assmQF->left(), subgoal, args, matching))
          {
            for (auto & a : matching) repl = replaceAll(repl, a.first, a.second);
            return replaceAll(subgoal, repl->left(), repl->right());
          }
        }
        if ((isOpX<LEQ>(assmQF) && isOpX<LEQ>(subgoal)) ||
            (isOpX<GEQ>(assmQF) && isOpX<GEQ>(subgoal)) ||
            (isOpX<LT>(assmQF) && isOpX<LT>(subgoal)) ||
            (isOpX<GT>(assmQF) && isOpX<GT>(subgoal)))
        {
          if (findMatchingSubexpr (assmQF->left(), subgoal->left(), args, matching))
          {
            for (auto & a : matching) repl = replaceAll(repl, a.first, a.second);
            if (u.implies(repl, subgoal)) return mk<TRUE>(efac);
          }
        }
      }
      else
      {
        // for a quantifier-free assumption (e.g., inductive hypotheses),
        // we create an SMT query and check with Z3
        // TODO: we can do so for ALL constistent quantifier-free assumptions at once
        if (u.implies(assm, subgoal)) return mk<TRUE>(efac);
        if (isOpX<EQ>(assm))
        {
          Expr res = replaceAll(subgoal, assm->left(), assm->right());
          if (res != subgoal)
          {
            return res;
          }
        }
      }
      // if nothing helped, return NULL -- it will be used for backtracking
      return NULL;
    }

    void useAssumptionMulti(Expr subgoal, Expr assm, ExprVector& results)
    {
      subgoal = liftITEs(subgoal);
      if (isOpX<FORALL>(assm))
      {
        ExprMap matching;
        ExprVector args;
        for (int i = 0; i < assm->arity() - 1; i++) args.push_back(bind::fapp(assm->arg(i)));
        Expr assmQF = assm->last();
        Expr repl = assmQF;

        // we first search for a matching of the entire assumption (usually some inequality)
        if (findMatchingSubexpr (assmQF, subgoal, args, matching))
        {
          for (auto & a : matching) repl = replaceAll(repl, a.first, a.second);
          Expr replaced = replaceAll(subgoal, repl, mk<TRUE>(efac));
          if (subgoal != replaced)
          {
            results.push_back(replaced);
            return;
          }
        }
        if (isOpX<EQ>(assmQF))
        {
          vector<ExprMap> matchings;
          findMultiMatchingSubexpr (assmQF->left(), subgoal, args, matchings);
          for (ExprMap &match: matchings)
          {
            repl = assmQF;
            for (auto & a : match) repl = replaceAll(repl, a.first, a.second);
            results.push_back(replaceAll(subgoal, repl->left(), repl->right()));
          }
        }
        if ((isOpX<LEQ>(assmQF) && isOpX<LEQ>(subgoal)) ||
            (isOpX<GEQ>(assmQF) && isOpX<GEQ>(subgoal)) ||
            (isOpX<LT>(assmQF) && isOpX<LT>(subgoal)) ||
            (isOpX<GT>(assmQF) && isOpX<GT>(subgoal)))
        {
          vector<ExprMap> matchings;
          findMultiMatchingSubexpr (assmQF->left(), subgoal, args, matchings);
          for (ExprMap &match: matchings)
          {
            repl = assmQF;
            for (auto & a : match) repl = replaceAll(repl, a.first, a.second);
            if (u.implies(repl, subgoal)) results.push_back(mk<TRUE>(efac));
          }
        }
      }
      else
      {
        // for a quantifier-free assumption (e.g., inductive hypotheses),
        // we create an SMT query and check with Z3
        // TODO: we can do so for ALL constistent quantifier-free assumptions at once
        if (u.implies(assm, subgoal)) results.push_back(mk<TRUE>(efac));
        if (isOpX<EQ>(assm))
        {
          Expr res = replaceAll(subgoal, assm->left(), assm->right());
          if (res != subgoal)
          {
            results.push_back(res);
          }
        }
      }
    }


    // this method is used when a strategy is specified from the command line
    bool tryStrategy(Expr subgoal, vector<int>& strat)
    {
      Expr subgoal_copy = subgoal;
      for (int i : strat)
      {
        assert (i < assumptions.size());
        subgoal_copy = useAssumption(subgoal_copy, assumptions[i]);
        if (subgoal_copy == NULL || subgoal_copy == subgoal) break;

        LOG(3, outs () << "rewritten [" << i << "]:   " << *subgoal_copy << "\n");
        if (u.isEquiv(subgoal_copy, mk<TRUE>(efac))) return true;
      }
      return false;
    }

    
    // Reduce Proving F(A,B,C ..., X) = F(A,B,C ..., Y) to Proving X = Y
    Expr rewriteTyTy(Expr eq)
    {
      if (!isOpX<EQ>(eq) || eq->arity() != 2) return eq;
      Expr lhs = eq->left();
      Expr rhs = eq->right();
      // if (!isOpX<FAPP>(lhs) || !isOpX<FAPP>(rhs) || (lhs->first() != rhs->first()) || lhs->arity() != 2) return eq;
      if (!isOpX<FAPP>(lhs) || !isOpX<FAPP>(rhs) || (lhs->first() != rhs->first()) || lhs->arity() < 2) return eq;

      int cntDiff = 0, diffArg = -1;
      for (int i = 1; i < lhs->arity(); i++){
        Expr larg = lhs->arg(i);
        Expr rarg = rhs->arg(i);
        if (larg != rarg){
          cntDiff ++;
          diffArg = i;
        }
      }
      
      // if (cntDiff == 1 && (lhs->first() == lhs->first()->arg())) 

      if (cntDiff == 1) {
        // Fn: Ty...->Ty
        Expr ty = lhs->first()->arg(1);
        int argN = 2;
        for (; argN < lhs->first()->arity(); argN++)
          if (ty != lhs->first()->arg(argN))
            break;
        if (argN == lhs->first()->arity())
          return mk<EQ>(lhs->arg(diffArg), rhs->arg(diffArg));
      }


      // if (lhs->first()->arg(1) == lhs->first()->arg(2))
      //   return mk<EQ>(lhs->arg(1), rhs->arg(1));
      return eq;
    }

    
    // this recursive method performs a naive search for a strategy
    bool rewriteAssumptions(Expr subgoal)
    {
      subgoal = replace(subgoal, mk_fn_map(SimplifyAdd0()));
      // Expr newGoal = rewriteITE(subgoal);
      // if (newGoal) subgoal = newGoal;
      subgoal = u.simplifyITE(subgoal);
      subgoal = rewriteTyTy(subgoal);
      // subgoal = rewriteImplication(subgoal);
      if (u.isEquiv(subgoal, mk<TRUE>(efac))) {
        LOG(2, outs()<<"Proof sequence:");
        LOG(2, for (int a : rewriteSequence) outs()<<" "<<a; outs()<<"\n");
        return true;
      }

      // check recursion depth
      if (rewriteSequence.size() >= cfg.maxSearchD) 
      {
        LOG(4, outs() << "  reached max search depth! \n");
        maxDepthCnt ++;
        return false;
      }
      
      // check consecutive applications of the same assumption
      if (rewriteSequence.size() >= cfg.maxSameAssm){
        int assmId = rewriteSequence.back();
        int offset = rewriteSequence.size() - cfg.maxSameAssm - 1;
        int i = 0;
        for (; i < cfg.maxSameAssm; i++)
          if (rewriteSequence[i + offset] != assmId)
            break;
        // test here
        if (i == cfg.maxSameAssm){
          LOG(4, outs() << "  same assm["<<assmId<<"] applied too many times! \n");
          return false;
        }
      }



      auto elapsed = std::chrono::system_clock::now() - begin;
      if (elapsed > maxTime){
        LOG(2, outs()<<"  TIME OUT!!!!\n");
        return false;
      }
      int branch = 0;
      bool noMoreRewriting = true;
      for (int i = 0; i < assumptions.size(); i++)
      {
        // only apply this rule when proving inductive case
        if (baseOrInd && cfg.flipIH && rewriteSequence.size()){
          int assmId = rewriteSequence.back();
          // IH and IH' cannot be applied back-to-back
          if ( ((assmId == assumptions.size() - 1) && (i == assmId - 1))
            || ((assmId == assumptions.size() - 2) && (i == assmId + 1)))
            continue;
          // TODO: IH and IH' can be applied to different part of the expression
        }
        Expr a = assumptions[i];
        ExprVector results;
        useAssumptionMulti(subgoal, a, results);
        for (Expr res : results)
        {
          if (res != NULL)
          {
            branch ++;
            // If revisit && no other assm can apply, still count as "noMoreRewriting" with more-fail moreFail
            if (rewriteSet.find(res) != rewriteSet.end()){
              LOG(5, outs()<<"  revisit\n");
              if (!cfg.moreFail) noMoreRewriting = false;
              continue;
            }
            noMoreRewriting = false;
            rewriteSet.insert(res);
            LOG(3, outs () << "rewritten [" << i << "]:   " << *res << "\n");
            // save history
            rewriteHistory.push_back(res);
            rewriteSequence.push_back(i);

            if  (rewriteAssumptions(res)){
              saveBranchFactor(branch);
              return true;
            }
            else {
              // failed attempt, remove history
              rewriteHistory.pop_back();
              rewriteSequence.pop_back();
              // backtrack:
              LOG(4, outs()<<"  bt\n");
            }
          }
        }
      }
      // failure node, stuck here, have to backtrack
      btCnt++;
      if (noMoreRewriting){
        int fcnt = failures.size();
        failures.insert(subgoal);
        if (fcnt < failures.size())
        {
          LOG(2, outs()<<"***new failure== "<< *subgoal<<"\nreached by: \n");
          LOG(2,
            for (int k = 0; k < rewriteSequence.size(); k ++)
              outs()<<"["<<rewriteSequence[k]<<"] "<<*(rewriteHistory[k])<<"\n"
          );
        }
        failureCnt ++;
      }
      saveBranchFactor(branch);
      return false;
    }

    // preprocessing of the main goal:
    //   - classify constructors for all ADTs that appear in the goal
    //   - replace all non-inductive ADTs
    void unfoldGoal()
    {

      ExprVector goalArgs;
      Expr unfoldedGoalQF = goal->last();
      bool toRebuild = false;
      for (int i = 0; i < goal->arity() - 1; i++)
      {
        Expr type = goal->arg(i)->last();
        for (auto & a : constructors)
        {
          if (a->last() == type)
          {
            bool ind = false;
            for (int i = 0; i < a->arity() - 1; i++)
            {
              if (a->last() == a->arg(i))
              {
                ind = true;
                if (!find_expr_mmap(indConstructors, type, a))
                  indConstructors.insert(make_pair(type, a));
              }
            }
            if (!ind)
            {
              if (!find_expr_mmap(baseConstructors, type, a))
                  baseConstructors.insert(make_pair(type, a));
            }
          }
          else // a ctor not quantified in goal, still need to init
          {
            bool ind = false;
            for (int i = 0; i < a->arity() - 1; i++)
            {
              if (a->last() == a->arg(i)) 
              {
                ind = true;
                Expr ty = a->last();
                if (!find_expr_mmap(indConstructors, ty, a))
                  indConstructors.insert(make_pair(ty, a));
                break;
              }
            }
            if (!ind)
            {
              Expr ty = a->last();
              if (!find_expr_mmap(baseConstructors, ty, a))
                  baseConstructors.insert(make_pair(ty, a));
            }
          }
        }
        if (baseConstructors.count(type) == 1 && indConstructors.count(type) == 0)
        {
          toRebuild = true;
          ExprVector args;
          Expr baseCtor = baseConstructors.find(type) -> second;
          args.push_back(baseCtor);
          for (int i = 1; i < baseCtor->arity() - 1; i++)
          {
            // TODO: make sure the name is unique
            Expr s = bind::mkConst(mkTerm<string>
                         ("_b_" + to_string(goalArgs.size()), efac),
                         baseCtor->arg(i));
            goalArgs.push_back(s->last());
            args.push_back(s);
          }
          Expr newApp = mknary<FAPP>(args);
          unfoldedGoalQF = replaceAll(unfoldedGoalQF, bind::fapp(goal->arg(i)), newApp);
        }
        else
        {
          goalArgs.push_back(goal->arg(i));
        }
      }

      if (toRebuild)
      {
        goalArgs.push_back(unfoldedGoalQF);
        goal = mknary<FORALL>(goalArgs);

        // continue recursively, because newly introduced vars may again need unfolding
        unfoldGoal();
      }
    }

    // this method can be (but not used currently) to add symmetric assumptions
    // and to enable searching for RHS of assumptions
    void insertSymmetricAssumption(Expr assm)
    {
      if (isOpX<EQ>(assm))
      {
        assumptions.push_back(mk<EQ>(assm->right(), assm->left()));
      }
      else if (isOpX<FORALL>(assm) && isOpX<EQ>(assm->last()))
      {
        ExprVector args;
        for (int i = 0; i < assm->arity() - 1; i++) args.push_back(assm->arg(i));
        args.push_back(mk<EQ>(assm->last()->right(), assm->last()->left()));
        assumptions.push_back(mknary<FORALL>(args));
      }
    }

    void printAssumptions()
    {
      outs () << "=========================\n";
      for (int i = 0; i < assumptions.size(); i++)
      {
        outs () << "Assumptions [" << i << "]: " << *assumptions[i] << "\n";
      }
    }

    bool induction(int num, vector<int>& basenums, vector<int>& indnums)
    {
      assert(num < goal->arity() - 1);
      Expr typeDecl = goal->arg(num);
      Expr type = goal->arg(num)->last();

      // instantiate every quantified variable (except the inductive one) in the goal
      Expr goalQF = goal->last();
      for (int i = 0; i < goal->arity() - 1; i++)
      {
        if (i == num) continue;
        // TODO: make sure the name is unique
        Expr s = bind::mkConst(mkTerm<string> ("_v_" + to_string(i) + "_sn" + to_string(_cntr), efac), goal->arg(i)->last());
        goalQF = replaceAll(goalQF, bind::fapp(goal->arg(i)), s);
      }

      // prove the base case
      // Expr baseConstructor = baseConstructors[type];
      auto range = baseConstructors.equal_range(type);
      for (auto iter = range.first; iter != range.second; ++iter)
      {
        Expr baseSubgoal = replaceAll(goalQF, typeDecl, iter->second);
        LOG(2, printAssumptions());
        LOG(1, outs() << "\nBase case "<< *baseSubgoal << "\n");
        rewriteSet.clear();
        rewriteSequence.clear();
        rewriteHistory.clear();
        maxDepthCnt = 0;
        failureCnt = 0;
        btCnt = 0;
        failures.clear();

        baseOrInd = false;

        begin = std::chrono::system_clock::now();
        bool baseres = basenums.empty() ?
                rewriteAssumptions(baseSubgoal) :
                tryStrategy(baseSubgoal, basenums);
        
        // remove baseSubgoal
        failures.erase(baseSubgoal);
        LOG(2, outs()<<"======== base # of leaves at max depth: "<<maxDepthCnt<<"\n");
        LOG(2, outs()<<"======== base # of failure nodes: "<<failureCnt<<"("<<btCnt<<")\n");
        LOG(2, outs()<<"======== base # of unique failure nodes: "<<failures.size()<<"\n");
        
        if (!baseres)
        {
          ExprVector newArgs;
          for (int i = 0; i < goal->arity() - 1; i++)
          {
            if (i == num) continue;
            newArgs.push_back(goal->arg(i));
          }
          if (newArgs.size() > 0)
          {
            LOG(1, outs () << "Proceeding to nested induction for base case\n");
            newArgs.push_back(replaceAll(goal->last(), typeDecl, iter->second));
            Expr newGoal = mknary<FORALL>(newArgs);
            ADTSolver sol (newGoal, assumptions, constructors, cfg);
            if (!sol.solve (basenums, indnums)) 
            {
              if (failures.empty()){
                importedFailure = true;
                LOG(2, outs()<<"Nested induction for base case Failed, logging failure points: "<<sol.failures.size()<<"\n"); 
                for (auto f: sol.failures)
                  LOG(2, outs()<<"Failure from nested induction: "<<*f<<"\n"); 
                failures.insert(sol.failures.begin(), sol.failures.end());
              }
              LOG(1, outs () << "Nested induction for base case failed!!!\n");
              return false;
            }
            LOG(1, outs () << "Returning to the outer induction\n\n");
          }
          else
          {
            return false;
          }
        }
      }
      // all base cased proved.

      // generate inductive hypotheses
      range = indConstructors.equal_range(type);
      failures.clear();
      for (auto iter = range.first; iter != range.second; ++iter)
      {
        Expr indConstructor = iter->second;
        ExprVector args;
        ExprVector indHypotheses;
        bool allQF = true;

        for (int i = 1; i < indConstructor->arity() - 1; i++)
        {
          // TODO: make sure the name is unique
          Expr s = bind::mkConst(mkTerm<string> ("_t_" + to_string(i) + "_sn" + to_string(_cntr), efac), indConstructor->arg(i));
          args.push_back(s);

          if (type == indConstructor->arg(i)) // type check
          {
            ExprVector argsIH;
            for (int j = 0; j < goal->arity() - 1; j++)
            {
              if (j != num) argsIH.push_back(goal->arg(j));
            }
            argsIH.push_back(replaceAll(goal->last(), bind::fapp(typeDecl), s));
            if (argsIH.size() == 1)
            {
              indHypotheses.push_back(argsIH.back());
            }
            else
            {
              allQF = false;
              indHypotheses.push_back(mknary<FORALL>(argsIH));
            }
          }
        }
        for (auto & a : indHypotheses) {
          assumptions.push_back(a);
          // always add symmetric IH?
          if (cfg.flipIH)
            insertSymmetricAssumption(a);
        }

        // for simplicity, add conjunction of hypotheses as a single hypothesis
        // should be removed in the future (when all QF-assumptions are used at the same time)
        if (indHypotheses.size() > 1 && allQF) assumptions.push_back(conjoin(indHypotheses, efac));

        // prove the inductive step
        Expr indConsApp = bind::fapp(indConstructor, args);
        Expr indSubgoal = replaceAll(goalQF, bind::fapp(typeDecl), indConsApp);
        LOG(2, printAssumptions());
        LOG(1, outs() << "Inductive case:  " << * indSubgoal << "\n");

        rewriteSet.clear();
        rewriteSequence.clear();
        rewriteHistory.clear(); // TODO: use it during the base case proving
        maxDepthCnt = 0;
        failureCnt = 0;
        btCnt = 0;
        // failures.clear();
        baseOrInd = true;
        begin = std::chrono::system_clock::now();

        branches = 0;
        nodes = 0;
        bool indres = indnums.empty() ?
                 rewriteAssumptions(indSubgoal) : // TODO: apply DFS, rank the failure nodes, synthesis of new lemma
                 tryStrategy(indSubgoal, indnums);

        LOG(0, outs()<<"******ind case branching factor:"<<(double)branches/nodes);
        failures.erase(indSubgoal);
        LOG(2, outs()<<"======== ind # of leaves at max depth: "<<maxDepthCnt<<"\n");
        LOG(2, outs()<<"======== ind # of failure nodes: "<<failureCnt<<"("<<btCnt<<")\n");
        LOG(2, outs()<<"======== ind # of unique failure nodes: "<<failures.size()<<"\n");

        if (indres) continue;
        else
        {
          ExprVector newArgs;
          for (int i = 0; i < goal->arity() - 1; i++)
          {
            if (i == num) continue;
            newArgs.push_back(goal->arg(i));
          }
          if (newArgs.size() > 0)
          {
            LOG(1, outs () << "Proceeding to nested induction for ind case\n");
            newArgs.push_back(replaceAll(goal->last(), bind::fapp(typeDecl), indConsApp));
            Expr newGoal = mknary<FORALL>(newArgs);
            ADTSolver sol (newGoal, assumptions, constructors, cfg);
            bool nestedRes = sol.solve (basenums, indnums);
            if (!nestedRes && failures.empty()){
              importedFailure = true;
              LOG(2, outs()<<"Nested induction for ind case Failed, logging failure points: "<<sol.failures.size()<<"\n"); 
              for (auto f: sol.failures)
                LOG(2, outs()<<"Failure from nested induction: "<<*f<<"\n"); 
              failures.insert(sol.failures.begin(), sol.failures.end());
            }

            if (nestedRes) continue;
            else return false;
          } else return false;
        }
      }
      // proved all ind cases
      return true;
    }

    bool isVarFn(Expr e){
      if (isOpX<FAPP> (e) && e->arity () == 1 && isOpX<FDECL> (e->first())) {
        return !(find_expr_mmap(baseConstructors, bind::typeOf(e), bind::fname(e)));
      } else return false;
    }
    bool isBaseCtorFn(Expr e){
      return (isOpX<FAPP> (e) && e->arity () == 1 && isOpX<FDECL> (e->first()) 
        && find_expr_mmap(baseConstructors, bind::typeOf(e), bind::fname(e)));
    }

    bool isIndCtorFn(Expr e){
      if (isOpX<FAPP> (e) && isOpX<FDECL> (e->first())){
        if (find(indCtorDecls.begin(), indCtorDecls.end(), e->first()) != indCtorDecls.end())
          return true;
      }
      return false;
    }
    void insertUniqueGoal(Expr goalQF, ExprVector& candidates) {
      goalQF = simplifyAdd(goalQF);
      goalQF = replace(goalQF, mk_fn_map(SimplifyAdd0()));
      ExprVector vars;
      filter(goalQF, [this](Expr e){return isVarFn(e);}, back_inserter(vars));
      if (vars.empty()) return;
      // remove fapp for quantified vars
      for (Expr &v : vars) v = v->first();
      vars.push_back(goalQF);
      Expr newGoal = mknary<FORALL>(vars);
      if (checkDuplicate(goal, newGoal)) return;
      if (find(candidates.begin(), candidates.end(), newGoal) == candidates.end())
      {
        candidates.push_back(newGoal);
        LOG(2, outs()<<" *** new lemma candidate:  "<<*newGoal<<"\n");
      }
    }
    Expr rewriteITE(Expr e)
    {
      if (!isOpX<EQ>(e) || e->arity() != 2) return NULL;
      Expr ite;
      if (isOpX<ITE>(e->left()))
      {
        ite = e->left();
        e = e->right();
      }else if (isOpX<ITE>(e->right())){
        ite = e->right();
        e = e->left();
      }else return NULL;

      // Expr thenBr = boolop::limp(ite->left(), mk<EQ>(e, ite->arg(1)));
      // Expr elseBr = boolop::limp(boolop::lneg(ite->left()), mk<EQ>(e, ite->arg(2)));
      Expr thenBr = mk<EQ>(ite->arg(1), e);
      Expr elseBr = mk<EQ>(ite->arg(2), e);
      if (u.isEquiv(thenBr, mk<TRUE>(efac))) return elseBr;
      if (u.isEquiv(elseBr, mk<TRUE>(efac))) return thenBr;
      else return NULL;
    }
    Expr genFapp(Expr eq) 
    {
      assert(isOpX<EQ>(eq) && "must be equality");
      Expr lhs = eq->first(), rhs = eq->last();
      auto isFapp = [this](Expr e){return isOpX<FAPP>(e) && e->arity() > 1;};

      ExprSet lFapp, rFapp;
      ExprVector fnApps;
      recFilter(lhs, isFapp, inserter(lFapp, lFapp.end()));
      recFilter(rhs, isFapp, inserter(rFapp, rFapp.end()));

      set_intersection(lFapp.begin(), lFapp.end(), rFapp.begin(), rFapp.end(), back_inserter(fnApps));
      Expr result = eq;
      if (!fnApps.empty())
      {
        Expr fapp = fnApps[0];
        Expr ty = bind::typeOf(fapp);
        string tyStr;
        if (isOpX<INT_TY>(ty)) tyStr = "INT";
        else tyStr = getTerm<string>(ty->first());
        Expr newVar = bind::mkConst(mkTerm<string>("_lm_fapp_" + tyStr, fapp->efac()), ty);
        result = replaceAll(eq, fapp, newVar);


        ExprVector fappArgs;
        filter(fapp, [this](Expr e){return isVarFn(e);}, back_inserter(fappArgs));
        bool replaceSuccess = true;
        for (Expr arg: fappArgs)
          if (contains(result, arg)){
            replaceSuccess = false;
            break;
          }
        if (cfg.genFapp == 3) replaceSuccess = true;
        if (!replaceSuccess) result = NULL;
      }
      return result;
    }
    void generalize(Expr goalQF, ExprVector &qVars, ExprVector &candidates)
    {
      if (treeSize(goalQF->first()) < treeSize(goalQF->last())){
        LOG(1, outs()<<"switch sides\n";);
        // fix: do not change operator
        goalQF = efac.mkBin(goalQF->op(), goalQF->last(), goalQF->first());
      }
      ExprVector ctorApps;
      filter(goalQF, [this](Expr e){return isIndCtorFn(e) && e->arity() > 2;}, back_inserter(ctorApps));
      if (!ctorApps.empty())
      {
        Expr ctor = ctorApps[0];
        ExprVector ctorArgs;
        filter(ctor, [this](Expr e){return isVarFn(e);}, back_inserter(ctorArgs));
        Expr ty = bind::typeOf(ctor);
        auto tyStr = getTerm<string>(ty->first());
        Expr newVar = bind::mkConst(mkTerm<string>("_lm_ind_" + tyStr, ctor->efac()), ty);
        LOG(4,outs()<<" <generalize> found ind ctor: "<<*ctor<<"\n");
        LOG(4,outs()<<"              replaced by newVar: "<<*newVar<<"\n");
        Expr newGoalQF = replaceAll(goalQF, ctor, newVar);

        bool replaceSuccess = true;
        if (isOpX<EQ>(goalQF))
        {
          bool ctorOnLHS = contains(goalQF->left(), ctor);
          bool ctorOnRHS = contains(goalQF->right(), ctor);
          if (!(ctorOnLHS && ctorOnRHS)) replaceSuccess = false;
        }
        if (replaceSuccess){
          for (Expr arg: ctorArgs)
          if (contains(newGoalQF, arg)){
            replaceSuccess = false;
            break;
          } 
        }
        if (replaceSuccess)
          insertUniqueGoal(newGoalQF, candidates);
        else
        {
          LOG(1, outs()<<" === generalize failed, prepare term enum\n");
          Expr LHS;
          if (isOpX<EQ>(newGoalQF))
            LHS = newGoalQF->first();
          else {
            LHS = goalQF;
            // strip away boolean predicates before term enum
            while (isOpX<BOOL_TY>(bind::typeOf(LHS))){
              if (isOpX<FAPP>(LHS))
                LHS = LHS->arg(1);
              else
                LHS = LHS->first();
            }
          }
          // replace base ctor
          ExprVector baseCtors;
          filter(LHS, [this](Expr e){return isBaseCtorFn(e);}, back_inserter(baseCtors));
          if (!baseCtors.empty()) {
            Expr baseCtor = baseCtors[0];
            Expr ty = bind::typeOf(baseCtor);
            auto tyStr = getTerm<string>(ty->first());
            Expr newVar = bind::mkConst(mkTerm<string>("_lm_base_" + tyStr, baseCtor->efac()), ty);
            LHS = replaceAll(LHS, baseCtor, newVar);
          }
          // generalize Function calls

          if (cfg.genFapp){
            ExprSet fnApps;
            recFilter(LHS, [this](Expr e){return isOpX<FAPP>(e) && e->arity() > 1;}, inserter(fnApps, fnApps.end()));
            vector<pair<int, Expr>> sortedFnApps;
            for (Expr e: fnApps){
              int sz = dagSize(e);
              LOG(4, outs()<<" <gen-fapp> found function application size "<<sz<<" "<<*e<<"\n");
              sortedFnApps.emplace_back(sz, e);
            } 
            std::sort(sortedFnApps.begin(), sortedFnApps.end(), 
              [](pair<int, Expr>& x, pair<int, Expr>& y){return x.first < y.first;});

            ExprVector LHSchoices;
            for (auto p : sortedFnApps)
            {
              Expr fapp = p.second;
              Expr ty = bind::typeOf(fapp);
              string tyStr;
              if (isOpX<INT_TY>(ty)) tyStr = "INT";
              else tyStr = getTerm<string>(ty->first());
              Expr newVar = bind::mkConst(mkTerm<string>("_lm_fapp_" + tyStr, fapp->efac()), ty);
              LHSchoices.push_back(replaceAll(LHS, fapp, newVar));
            }
            if (LHSchoices.size() == 0) LHS = newGoalQF->first();
            else LHS = LHSchoices[cfg.genFapp - 1];
          }
          Expr lhsTy = bind::typeOf(LHS);
          
          // use <??>+<??> for Int
          if (isOpX<INT_TY>(lhsTy)) cfg.lemmaTmpl = 2;
          else cfg.lemmaTmpl = 1;

          ExprSet lhsVars;
          filter(LHS, [this](Expr e){return isVarFn(e);}, inserter(lhsVars, lhsVars.end()));

          TermEnumerator tEnum(LHS, baseConstructors, indConstructors, cfg.maxTermDepth, cfg.noCtor);
          // MAYBE collect all functions
          // for (Expr assm : assumptions)
          //   tEnum.addFunctions(assm);
          tEnum.getTerms();
          ExprVector &tList = tEnum.allTerms[lhsTy];
          int validCnt = tList.size();
          LOG(2, outs()<<" === # terms "<<validCnt<<"\n");
          if (cfg.lemmaTmpl == 1) {
          /* TEMPLATE 1
           * LHS fixed = <???>
           * fill RHS
           */
            LOG(1, outs()<<" using template 1\n");
            for (int i = 0; i < validCnt; i ++) {
              ExprSet rhsVars;
              filter(tList[i], [this](Expr e){return isVarFn(e);}, inserter(rhsVars, rhsVars.end()));
              // same set of vars, not the same expr
              if (rhsVars == lhsVars && LHS != tList[i])
                insertUniqueGoal(mk<EQ>(LHS, tList[i]), candidates);
            }
          }else if (cfg.lemmaTmpl == 2) {
          /* TEMPLATE 2
           * LHS fixed = <???> + <???> for Int
           * fill RHS x 2
           */
            LOG(1, outs()<<" using template 2\n");
            assert(isOpX<INT_TY>(lhsTy) && "must be INT");
            for (int i = 0; i < validCnt; i ++)
              for (int j = i; j < validCnt; j++) {
                Expr RHS = mk<PLUS>(tList[i], tList[j]);
                ExprSet rhsVars;
                filter(RHS, [this](Expr e){return isVarFn(e);}, inserter(rhsVars, rhsVars.end()));
                // same set of vars, not the same expr
                if (rhsVars == lhsVars && RHS != LHS)
                  insertUniqueGoal(mk<EQ>(LHS, RHS), candidates);
              }
          }
          else {
            assert(0 && "unsurported lemma template");
          }
          // usually once is enough
        }
      }
      
      if (ctorApps.empty()) {
        LOG(1, outs()<<" *** attempt rewrite ITE and simplify arithmetic\n");
        if (!isOpX<EQ>(goalQF)) 
        {
          Expr LHS = goalQF->left(); 
          ExprSet fnApps;
          Expr fapp;
          recFilter(LHS, [this](Expr e){return isOpX<FAPP>(e) && e->arity() > 1;}, inserter(fnApps, fnApps.end()));
          int minSz = -1;
          for (Expr e: fnApps){
            int sz = dagSize(e);
            LOG(4, outs()<<" <gen-fapp> found function application size "<<sz<<" "<<*e<<"\n");
            if (minSz == -1 || sz < minSz) {
              fapp = e;
              minSz = sz;
            }
          }
          Expr fappTy = bind::typeOf(fapp); 
          string tyStr;
          if (isOpX<INT_TY>(fappTy)) tyStr = "INT";
          else tyStr = getTerm<string>(fappTy->first());
          Expr newVar = bind::mkConst(mkTerm<string>("_lm_fapp_" + tyStr, fapp->efac()), fappTy);
          LHS = replaceAll(LHS, fapp, newVar);
          Expr lhsTy = bind::typeOf(LHS);
          // use <??>+<??> for Int
          if (isOpX<INT_TY>(lhsTy)) cfg.lemmaTmpl = 2;
          else cfg.lemmaTmpl = 1;

          ExprSet lhsVars;
          filter(LHS, [this](Expr e){return isVarFn(e);}, inserter(lhsVars, lhsVars.end()));
          TermEnumerator tEnum(LHS, baseConstructors, indConstructors, cfg.maxTermDepth, cfg.noCtor);
          tEnum.getTerms();
          ExprVector &tList = tEnum.allTerms[lhsTy];
          int validCnt = tList.size();
          LOG(2, outs()<<" === # terms "<<validCnt<<"\n");
          if (cfg.lemmaTmpl == 1) {
          /* TEMPLATE 1
           * LHS fixed = <???>
           * fill RHS
           */
            LOG(1, outs()<<" using template 1\n");
            for (int i = 0; i < validCnt; i ++) {
              ExprSet rhsVars;
              filter(tList[i], [this](Expr e){return isVarFn(e);}, inserter(rhsVars, rhsVars.end()));
              // same set of vars, not the same expr
              if (rhsVars == lhsVars && LHS != tList[i])
                insertUniqueGoal(mk<EQ>(LHS, tList[i]), candidates);
            }
          }else if (cfg.lemmaTmpl == 2) {
          /* TEMPLATE 2
           * LHS fixed = <???> + <???> for Int
           * fill RHS x 2
           */
            LOG(1, outs()<<" using template 2\n");
            assert(isOpX<INT_TY>(lhsTy) && "must be INT");
            for (int i = 0; i < validCnt; i ++){
              Expr RHS = mk<PLUS>(tList[i], mkTerm<mpz_class>(1, efac));
              insertUniqueGoal(mk<EQ>(LHS, RHS), candidates);
            }
            for (int i = 0; i < validCnt; i ++)
              for (int j = i; j < validCnt; j++) {
                Expr RHS = mk<PLUS>(tList[i], tList[j]);
                ExprSet rhsVars;
                filter(RHS, [this](Expr e){return isVarFn(e);}, inserter(rhsVars, rhsVars.end()));
                // same set of vars, not the same expr
                if (rhsVars == lhsVars && RHS != LHS)
                  insertUniqueGoal(mk<EQ>(LHS, RHS), candidates);
              }

          }
          else {
            assert(0 && "unsurported lemma template");
          }
        }else{
          if (cfg.lemmaTmpl == 3){
            /* TEMPLATE 3
             * <???> = <???>
             */
             LOG(1, outs()<<" using template 3\n");
            ExprSet reqVars;
            filter(goalQF, [this](Expr e){return isVarFn(e);}, inserter(reqVars, reqVars.end()));

            ExprSet reqFns;
            auto isFuncFn = [](Expr e){return isOpX<FDECL> (e) && e->arity () >= 3;};
            filter(goalQF, isFuncFn, inserter(reqFns, reqFns.end()));
            
            TermEnumerator tEnum(goalQF, baseConstructors, indConstructors, cfg.maxTermDepth, cfg.noCtor);
            tEnum.getTerms();
            ExprVector &tList = tEnum.allTerms[bind::typeOf(goalQF->left())];
            int termsCnt = tList.size();
            LOG(2, outs()<<" === # terms "<<termsCnt<<"\n");
            for (int i = 0; i < termsCnt; i++)
              for (int j = i + 1; j < termsCnt; j++) {
                ExprSet lhsVars;
                filter(tList[i], [this](Expr e){return isVarFn(e);}, inserter(lhsVars, lhsVars.end()));
                if (lhsVars != reqVars) continue;
                ExprSet rhsVars;
                filter(tList[j], [this](Expr e){return isVarFn(e);}, inserter(rhsVars, rhsVars.end()));
                if (rhsVars != reqVars) continue;
                ExprSet lhsFns;
                filter(tList[i], isFuncFn, inserter(lhsFns, lhsFns.end()));
                if (lhsFns != reqFns) continue;
                ExprSet rhsFns;
                filter(tList[j], isFuncFn, inserter(rhsFns, rhsFns.end()));
                if (rhsFns != reqFns) continue;
                // same set of vars, not the same expr
                insertUniqueGoal(mk<EQ>(tList[i], tList[j]), candidates);
              }
          }
          goalQF = replace(goalQF, mk_fn_map(SimplifyAdd0()));
          // Expr simplGoal = rewriteITE(goalQF);
          // if (simplGoal) goalQF = simplGoal;
          goalQF = u.simplifyITE(goalQF);
          goalQF = genFapp(goalQF);
          if (goalQF) insertUniqueGoal(goalQF, candidates);
        }

      }
    }
    int cntFuncFn(Expr e){
      ExprSet funcs;
      filter(e, [](Expr e){return isOpX<FDECL> (e) && e->arity () >= 3;}, 
        inserter(funcs, funcs.end()));
      return funcs.size();
    }

    void resetValues(){
      _nextInt = 0;
      valueMap.clear();
    }
    Expr getNextValue(Expr ty)
    {
      if (isOpX<INT_TY>(ty))
        return mkTerm<mpz_class>(++_nextInt, efac);
      else {
        if (valueMap.count(ty) == 0){
          // enumeration not complete for multi-base
          valueMap[ty] = bind::fapp(baseConstructors.find(ty)->second);
        }
        Expr currentValue = valueMap[ty];
        // enumeration not complete for multi-ind
        if (indConstructors.count(ty) == 0) return currentValue;
        Expr indCtorDecl = indConstructors.find(ty)->second;

        ExprVector args;
        args.push_back(indCtorDecl);
        for (int i = 1; i < indCtorDecl->arity() - 1; ++i)
        {
          Expr argTy = indCtorDecl->arg(i);
          if (argTy == ty) args.push_back(currentValue);
          else args.push_back(getNextValue(argTy));
        }
        currentValue = mknary<FAPP>(args);
        valueMap[ty] = currentValue;
        return currentValue;
      }
    }

    bool checkDuplicate(Expr formulaA, Expr formulaB)
    {
      assert(isOpX<FORALL>(formulaA) && isOpX<FORALL>(formulaB));
      if (formulaA->arity() != formulaB->arity()) return false;
      Expr qfA = formulaA->last(), qfB = formulaB->last();
      for (int i = 0; i < formulaA->arity() - 1; i++)
        qfA = replaceAll(qfA, formulaA->arg(i), formulaB->arg(i));
      if (qfA == qfB)
        return true;
      else return false;
    }
    void tryAssociativity(Expr fail, ExprVector& candidates)
    {
      // CALL ONCE!!!!
      if (_triedAssoc) return;
      else _triedAssoc = true;
      ExprVector funcs;
      // hack: get all named functions
      fail = mknary<FORALL>(assumptions);


      // find functions of type (A, A)->A
      filter(fail, [](Expr e){
        return isOpX<FDECL> (e) && e->arity () == 4
          && e->arg(1) == e->last() && e->arg(2) == e->last() ;}, 
        back_inserter(funcs));
      for (Expr fdecl : funcs)
      {
        Expr ty = fdecl->last();
        string tyStr = getTerm<string>(ty->first());
        Expr x = bind::mkConst(mkTerm<string>("_assoc_x_" + tyStr, efac), ty);
        Expr y = bind::mkConst(mkTerm<string>("_assoc_y_" + tyStr, efac), ty);
        Expr z = bind::mkConst(mkTerm<string>("_assoc_z_" + tyStr, efac), ty);
        Expr assocRule = mk<EQ>(bind::fapp(fdecl, bind::fapp(fdecl, x, y), z), bind::fapp(fdecl, x, bind::fapp(fdecl, y, z)));
        insertUniqueGoal(assocRule, candidates);
      }
    }

    void tryCommutativity(Expr fail, ExprVector& candidates)
    {
      // CALL ONCE!!!!
      if (_triedComm) return;
      else _triedComm = true;
      ExprVector funcs;

      // hack: get all named functions
      fail = mknary<FORALL>(assumptions);

      // find functions of type (A, A)->A
      filter(fail, [](Expr e){
        return isOpX<FDECL> (e) && e->arity () == 4
          && e->arg(1) == e->last() && e->arg(2) == e->last() ;}, 
        back_inserter(funcs));
      for (Expr fdecl : funcs)
      {
        Expr ty = fdecl->last();
        string tyStr = getTerm<string>(ty->first());
        Expr x = bind::mkConst(mkTerm<string>("_comm_x_" + tyStr, efac), ty);
        Expr y = bind::mkConst(mkTerm<string>("_comm_y_" + tyStr, efac), ty);
        Expr commRule = mk<EQ>(bind::fapp(fdecl, x, y), bind::fapp(fdecl, y, x));
        insertUniqueGoal(commRule, candidates);
      }
    }
    bool tryLemmas(Expr originaGoal, ExprVector assm, bool tryAgain = true)
    {

      vector<int> basenums;
      vector<int> indnums;
      /*if (failures.empty()) {
        LOG(0, outs()<<"ATTENTION!!! max search depth not enough to reach failure points!!\n");
        cfg.maxSearchD += 5;
        if (cfg.maxSearchD < 30)
        {
          ADTSolver deeperSol (originaGoal, assm, constructors, cfg);
          bool result = deeperSol.solve(basenums, indnums);
          if (result) return true;
          else return deeperSol.tryLemmas(originaGoal, assm, tryAgain);
        }
      }*/
      ExprVector candidates;

      // rank failures. less functions the better
      vector<pair<int, Expr>> sortedF;
      for (Expr f : failures){
        sortedF.emplace_back(cntFuncFn(f), f);
      }
      std::sort(sortedF.begin(),sortedF.end(), 
        [](pair<int, Expr>& x, pair<int, Expr>& y){return x.first < y.first;});
      for (auto x : sortedF)
      {
        Expr f = x.second;
        LOG(1, outs()<<"** lemma synth on failure "<<*f<<"\n");
        ExprVector vars;
        ExprVector renamedVars;
        filter(f, [this](Expr e){return isVarFn(e);}, back_inserter(vars));
        for (Expr v: vars)
        {
          Expr varDecl = v->left();
          auto nameStr = "_lm" + getTerm<string>(varDecl->left());
          Expr newName = mkTerm<string>(nameStr, v->efac());
          renamedVars.push_back(bind::fapp(bind::rename(varDecl, newName)));
        }
        Expr goalQF = replaceAll(f, vars, renamedVars);
        if (cfg.tryComm) tryCommutativity(goalQF, candidates);
        if (cfg.tryAssoc) tryAssociativity(goalQF, candidates);
        
        if (importedFailure) insertUniqueGoal(goalQF, candidates);
        else generalize(goalQF, renamedVars, candidates);
        // ExprVector mkLemma = renamedVars;
        // mkLemma.push_back(goalQF);
        // Expr lemmaAsIs = mknary<FORALL>(mkLemma);
        // bool trivial = false;
        // for (int i = 0; i < cfg.presolveTimes; i++)
        //   if (simplifyGoal(lemmaAsIs)) {
        //     trivial = true;
        //     break;
        //   }
        // if (!trivial)
        //   generalize(goalQF, renamedVars, candidates);
        //break;
      }
      bool assoc_only = false;
      if (failures.empty()) {
        LOG(0, outs()<<"ATTENTION!!! max search depth not enough to reach failure points!!\n");
        if (cfg.tryComm) tryCommutativity(originaGoal, candidates);
        if (cfg.tryAssoc) tryAssociativity(originaGoal, candidates);
        assoc_only = true;
      }
      

      bool res;
      LOG(1, outs()<<"\n\n======== # of lemma candidates "<<candidates.size()<< "\n\n");
      int lemma_cntr = 0;
      for (Expr lemma: candidates) {
        lemma_cntr ++;
        res = true;
        int nQVars = lemma->arity() - 1;
        int nTest = cfg.refuteTests;
        resetValues();
        LOG(3, outs()<<" try refute lemma: "<<*lemma<<"\n");
        while (nTest--) {
          Expr lemmaQF = lemma->last();
          for (int i = 0; i < nQVars; i++) {
            Expr qVar = bind::fapp(lemma->arg(i));
            Expr ty = bind::typeOf(qVar);
            lemmaQF = replaceAll(lemmaQF, qVar, getNextValue(ty));
          }
          // bad lemma
          if (refuteGoal(lemmaQF, cfg.refuteSimpl) == false)  break;  
        }

        // some test failed
        if (nTest != -1) continue;
        LOG(3, outs()<<" lemma passes tests: "<<*lemma<<"\n");
        
        LOG(1, outs()<<"======={ try proving lemma\n");
        ADTSolver solLemma (lemma, assm, constructors, cfg);
        res = solLemma.solve (basenums, indnums);
        if (!res) {

          LOG(1, outs()<<" ****** not solved. attempt lemma synth on proposed lemma\n");
          res = solLemma.tryLemmas(lemma, assumptions, false);
          if (!res) {
            LOG(1, outs()<<"\n======= lemma is invalid / not proved }\n");
            continue;
          }else{
            for (Expr l : solLemma.newLemmas) assm.push_back(l);
          }
        }

        
        LOG(1, outs()<<"========lemma is valid and proved}\n");
        assm.push_back(lemma);
        newLemmas.push_back(lemma);
        Expr firstV = lemma->first();
        if (!assoc_only)
        {
          string varName = getTerm<string>(firstV->left());
          if (varName.substr(0, 9) == "_assoc_x_" 
            ||varName.substr(0, 8) == "_comm_x_" )
            if (lemma_cntr != candidates.size())
            continue;
        }
        
        ADTSolver sol (originaGoal, assm, constructors, cfg);
        LOG(1, outs()<<"======={ try original goal with lemma\n");
        res = sol.solve (basenums, indnums);
        if (res) {
          LOG(1, outs()<<"===========Solved with new lemma: "<< *lemma <<"}\n");
          return true;
        }else {
          LOG(1, outs()<<"===========Not solved with new lemma: "<< *lemma <<"}\n");
          if (tryAgain) {
            LOG(1, outs()<<"===========tryLemmas 2nd attempt begin{\n");
            res = sol.tryLemmas(originaGoal, assm, false);
            LOG(1, outs()<<"===========tryLemmas 2nd attempt end}\n");
            if (res) return true;
          }
        }
      }

      return false;
    }

    bool solve(vector<int>& basenums, vector<int>& indnums)
    {
      unfoldGoal();
      rewriteHistory.clear();
      rewriteHistory.push_back(goal);
      for (int i = 0; i < cfg.presolveTimes; i++)
      {
        if (simplifyGoal(goal))
        {
          LOG(1, outs () << "Trivially Proved\n");
          return true;
        }
      }

      for (auto p : indConstructors)
      {
        if (isOpX<AD_TY>(p.first) && p.second != NULL)
          indCtorDecls.insert(p.second);
      }

      // simple heuristic: if the result of every rewriting made the goal larger, we rollback
      /*bool toRollback = true;
      for (int i = 1; i < rewriteHistory.size(); i++)
      {
        toRollback = toRollback &&
            (treeSize(rewriteHistory[i-1]) < treeSize(rewriteHistory[i]));
      }

      if (toRollback) goal = rewriteHistory[0];*/
      if (treeSize(goal) >= treeSize(rewriteHistory[0])) goal = rewriteHistory[0];

      LOG(1, outs () << "Simplified goal: " << *goal << "\n");

      for (int i = 0; i < goal->arity() - 1; i++)
      {
        Expr type = goal->arg(i)->last();
        if (baseConstructors.count(type) + indConstructors.count(type) > 0)
        {
          if (induction(i, basenums, indnums))
          {
            LOG(1, outs () << "                 Proved with induction\n");
            return true;
          }
          else
          {
            LOG(1, outs () << "                 Failed\n");
            return false;
          }

        }
      }
      return false;
    }
  };

  int ADTSolver::_cntr = 0;
  bool ADTSolver::_triedAssoc = false;
  bool ADTSolver::_triedComm = false;
  static inline void getNums(vector<int>& nums, char * str)
  {
    if (str == NULL) return;
    int len = strlen(str);
    char* pch = strchr(str, ',');
    int pos1 = 0;
    int pos2 = 0;
    while (pch != NULL)
    {
      pos2 = pch - str;
      char* substr = (char*)malloc(pos2 - pos1);
      strncpy(substr, str + pos1, pos2 - pos1);
      nums.push_back(atoi(substr));
      pch = strchr(pch + 1, ',');
      pos1 = pos2 + 1;
    }
    if (pos1 == len) return;
    char* substr = (char*)malloc(len - pos1);
    strncpy(substr, str + pos1, len - pos1);
    nums.push_back(atoi(substr));
  }

  bool adtSolve(EZ3& z3, Expr s, char* basecheck, char *indcheck, Config cfg)
  {
    vector<int> basenums;
    vector<int> indnums;
    getNums(basenums, basecheck);
    getNums(indnums, indcheck);
    ExprVector constructors;
    for (auto & a : z3.getAdtConstructors()) constructors.push_back(regularizeQF(a));

    ExprVector assumptions;
    Expr goal;

    if (isOpX<AND>(s))
    {
      for (int i = 0; i < s->arity(); i++)
      {
        Expr a = s->arg(i);
        if (isOpX<NEG>(a))
        {
          goal = regularizeQF(a->left());
        }
        else
        {
          assumptions.push_back(regularizeQF(a));
        }
      }
    }
    else if (isOpX<NEG>(s))
    {
      goal = regularizeQF(s->left());
    }

    if (goal == NULL)
    {
      LOG(1, outs () << "Unable to parse the query\n");
      return false;
    }
    ADTSolver sol (goal, assumptions, constructors, cfg);

    bool res = sol.solve (basenums, indnums);
    if (!res){
      LOG(1, outs()<<" *** not solved. attempt lemma synth\n");
      res = sol.tryLemmas(goal, assumptions, true);
    }
    return res;
  }
}

#endif
