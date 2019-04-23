#ifndef CANDCHECKER__HPP__
#define CANDCHECKER__HPP__

#include "ae/SMTUtils.hpp"
#include "Horn.hpp"

using namespace std;
using namespace boost;
namespace ufo
{
  class CandChecker
  {
    private:

    ExprFactory &efac;
    EZ3 z3;
    ufo::ZSolver<ufo::EZ3> smt_solver;

    HornRuleExt* tr;
    HornRuleExt* fc;
    HornRuleExt* qr;

    ExprVector& vars;
    ExprSet learnedExprs;

    public:
    
    CandChecker (ExprFactory &_efac, HornRuleExt* _fc, HornRuleExt* _tr, HornRuleExt* _qr) :
      efac(_efac), z3(efac), smt_solver (z3), fc(_fc), tr(_tr), qr(_qr), vars(qr->srcVars)
    {
      // sanity checks:
      assert (fc != NULL);
      assert (tr != NULL);
      assert (qr != NULL);
      for (int i = 0; i < tr->srcVars.size(); i++)
        assert (tr->srcVars[i] == vars[i]);
      for (int i = 0; i < tr->dstVars.size(); i++)
        assert (tr->dstVars[i] == fc->dstVars[i]);
    }

    Expr getModel(ExprVector& vars)
    {
      // used to explain the reason why some of the check failed
      // i.e., it is supposed to be called after "smt_solver.solve()" returned SAT

      ExprVector eqs;
      ZSolver<EZ3>::Model m = smt_solver.getModel();
      for (auto & v : vars)
        if (v != m.eval(v))
            eqs.push_back(mk<EQ>(v, m.eval(v)));
      return conjoin (eqs, efac);
    }

    Expr getlearnedLemmas()
    {
      return conjoin (learnedExprs, efac);
    }

    bool checkInitiation(Expr cand)
    {
      for (int j = 0; j < fc->dstVars.size(); j++)
      {
        cand = replaceAll(cand, vars[j], fc->dstVars[j]);
      }

      smt_solver.reset ();
      smt_solver.assertExpr (fc->body);
      smt_solver.assertExpr (mk<NEG>(cand));

      return (!smt_solver.solve ());
    }

    bool checkInductiveness(Expr cand)
    {
      // supposed to be called after checkInitiation

      Expr candPrime = cand;

      for (int j = 0; j < fc->dstVars.size(); j++)
      {
        candPrime = replaceAll(candPrime, vars[j], tr->dstVars[j]);
      }

      smt_solver.reset ();
      smt_solver.assertExpr (tr->body);
      smt_solver.assertExpr (cand);
      smt_solver.assertExpr (getlearnedLemmas()); // IMPORTANT: use all lemmas learned so far
      smt_solver.assertExpr (mk<NEG>(candPrime));

      bool res = !smt_solver.solve ();
      if (res) learnedExprs.insert (cand);  // inductiveness check passed; so add a new lemma

      return res;
    }

    bool checkSafety()
    {
      // supposed to be called after checkInductiveness
      // but it does not take a candidate as input since it is already in learnedExprs

      smt_solver.reset();
      smt_solver.assertExpr (qr->body);
      smt_solver.assertExpr (getlearnedLemmas());

      return !smt_solver.solve ();
    }
  };
  
  inline void simpleCheck(const char * chcfile)
  {
    ExprFactory efac;
    EZ3 z3(efac);
    CHCs ruleManager(efac, z3);
    ruleManager.parse(string(chcfile));
    Expr cand = mk<TRUE>(efac);

    HornRuleExt* tr;
    HornRuleExt* fc;
    HornRuleExt* qr;

    for (auto & a : ruleManager.chcs)
      if (a.isInductive) tr = &a;
      else if (a.isFact) fc = &a;
      else if (a.isQuery) qr = &a;

    CandChecker cc(efac, fc, tr, qr);

    ExprSet cands;

    // collect vars/constants by width
    std::map<unsigned, ExprVector> bvVarsByWidth;
    std::map<unsigned, ExprVector> bvConstantsByWidth;


    for (auto & a: tr->srcVars)
    {
      if (bv::is_bvconst(a))
      {
        bvVarsByWidth[bv::width(a)].push_back(a);
      }
      else if (bind::isBoolConst(a)) {
        bvConstantsByWidth[bv::width(a)].push_back(a);
      }
    }
    // test commit
    for (auto & width_vars_pair : bvVarsByWidth) {
      // EQ between vars of the same width :    bv == bv
      unsigned width = width_vars_pair.first;
      auto & bvVars = width_vars_pair.second;
      for (int i = 0; i < bvVars.size(); i++)
        for (int j = i + 1; j < bvVars.size(); j++)
          cands.insert(mk<EQ>(bvVars[i], bvVars[j]));

      if (bvConstantsByWidth.find(width) != bvConstantsByWidth.end()) {
        auto & bvCnsts = bvConstantsByWidth[width];
         // if there are also constants
         // why not try v == constant
        for (int i = 0; i < bvVars.size(); i++)
          for (int j = i + 1; j < bvCnsts.size(); j++)
            cands.insert(mk<EQ>(bvVars[i], bvCnsts[j]));
      }
    }

    // check for simple candidates, if done we are good
    for (auto & cand : cands)
    {
      if (cc.checkInitiation(cand) &&
          cc.checkInductiveness(cand) &&
          cc.checkSafety())
      {
        outs() << "done\n";
        return;
      }
    }

    // what's the format to make a constant?
    

  }
}

#endif
