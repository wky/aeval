#ifndef CANDCHECKER__HPP__
#define CANDCHECKER__HPP__

#include "ae/SMTUtils.hpp"
#include "Horn.hpp"
#include <getopt.h>

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

    bool isSimplifyToConst(Expr c) {
      smt_solver.reset();
      smt_solver.assertExpr(c);
      bool possible_to_be_true = smt_solver.solve ();

      smt_solver.reset();
      smt_solver.assertExpr(mk<NEG>(c));
      bool possible_to_be_false = smt_solver.solve ();
      if (! (possible_to_be_true && possible_to_be_false) )
        return true; // if it cannot be true or cannot be false then it is const
      return false;
    }

    void serializeInvars()
    {
      Expr lms = getlearnedLemmas();
      for (auto & a : qr->origNames) lms = replaceAll(lms, a.first, a.second);

      smt_solver.reset();
      smt_solver.assertExpr(lms);

      smt_solver.toSmtLib (errs());
      errs().flush ();
    }

    string printExpr(Expr e)
    {
      for (auto & a : qr->origNames) e = replaceAll(e, a.first, a.second);
      std::stringstream sbuf;
      sbuf << e;
      return sbuf.str();
    }

  };

  static int OP_CONJ = 1;
  static int OP_DISJ = 2;

  void enumConstPredForEachVar(ExprVector& vars, unsigned bw_bound, vector<ExprVector>& lol){
    for (Expr v : vars){
      ExprVector preds;
      
      unsigned bw = bv::width(v->first()->arg(1));
      // std::stringstream sbuf;
      // sbuf<<"BV name: "<<v<<" width:"<<real_bw<<"\n";
      // cout<<sbuf.str();
      // unsigned bw = real_bw;
      Expr ev = v;
      if (bw > bw_bound)
      {
        bw = bw_bound;
        ev = bv::extract(bw-1, 0, v);
      }

      for (unsigned i = 0; i < (1ul<<bw); i++){
        Expr pred = mk<EQ>(ev, bv::bvnum(i, bw, v->efac()));
        preds.push_back(pred);
        pred = mk<NEQ>(ev, bv::bvnum(i, bw, v->efac()));
        preds.push_back(pred);
      }
      lol.push_back(preds);
    }
  }
  void enumDataPredForEachVar(ExprVector& LHSvars, unsigned bw_bound, ExprVector& RHSvars, vector<ExprVector>& lol){
    for (Expr v : LHSvars){
      ExprVector preds;
      Expr ev = v;
      unsigned bw = bv::width(v->first()->arg(1));
      if (bw > bw_bound) {
        bw = bw_bound;
        ev = bv::extract(bw-1, 0, v);
      }
      for (unsigned i = 0; i < (1ul<<bw); i++){
        Expr pred = mk<EQ>(ev, bv::bvnum(i, bw, v->efac()));
        preds.push_back(pred);
      }
      // X = Y
      bw = bv::width(v->first()->arg(1));
      for (Expr rhs: RHSvars) {
        unsigned rbw = bv::width(rhs->first()->arg(1));
        if (bw == rbw)
          preds.push_back(mk<EQ>(v, rhs));
        else if (bw > rbw)
          preds.push_back(mk<EQ>(bv::extract(rbw-1, 0, v), rhs));
        else if (bw < rbw)
          preds.push_back(mk<EQ>(v, bv::extract(bw-1, 0, rhs)));
      }
      // X = Y1 ADD Y2
      for (int i = 0; i < RHSvars.size(); i++){
        unsigned rbw1 = bv::width(RHSvars[i]->first()->arg(1));
        for (int j = i + 1; j < RHSvars.size(); j++){
          
          unsigned min_bw = bw; if (min_bw > rbw1) min_bw = rbw1;
          
          unsigned rbw2 = bv::width(RHSvars[j]->first()->arg(1));
          if (min_bw > rbw2) min_bw = rbw2;

          Expr X = bw == min_bw? v: bv::extract(min_bw-1, 0, v);
          Expr Y1 = rbw1 == min_bw? RHSvars[i]: bv::extract(min_bw-1, 0, RHSvars[i]);
          Expr Y2 = rbw2 == min_bw? RHSvars[j]: bv::extract(min_bw-1, 0, RHSvars[j]);

          preds.push_back(mk<EQ>(X, mk<BADD>(Y1, Y2)));
        }
      }
      // can have more operations

      lol.push_back(preds);
    }
  }
  Expr combineListExpr(ExprVector selection, int op){
    Expr e;
    if (selection.size() == 1) e = selection[0];
    else if (selection.size() == 2){
      if (op == OP_CONJ) e = mk<AND>(selection[0], selection[1]);
      else if (op == OP_DISJ) e = mk<OR>(selection[0], selection[1]);
    }
    else{
      if (op == OP_CONJ) e = mknary<AND>(selection);
      else if (op == OP_DISJ) e = mknary<OR>(selection);
    }
    return e;
  }
  

  void enumSelectFromLoLImplPart2(vector<ExprVector>& lol, int start, vector<int>& list_selection, ExprVector& selection, ExprVector& output, int op)
  {
    if (start == list_selection.size()){
      assert(selection.size() == list_selection.size());
      
      output.push_back(combineListExpr(selection, op));
      return;
    }
    for (Expr e: lol[list_selection[start]]) {
      selection.push_back(e);
      enumSelectFromLoLImplPart2(lol, start+1, list_selection, selection, output, op);
      selection.pop_back();
    }
  }

  void enumSelectFromLoLImpl(vector<ExprVector>& lol, int start, unsigned k, vector<int>& list_selection, ExprVector& output, int op)
  {
    if (k == 0){
      ExprVector selection;
      enumSelectFromLoLImplPart2(lol, 0, list_selection, selection, output, op);
      return;
    }
    for (int i = start; i <= lol.size() - k; ++i) {
      list_selection.push_back(i);
      enumSelectFromLoLImpl(lol, i+1, k-1, list_selection, output, op);
      list_selection.pop_back();
    }
  }
  
  void enumSelectKFromListofList(vector<ExprVector>& lol, unsigned k, ExprVector& output, int op){
    vector<int> list_selection;
    for (int i = 1; i <= k; i++)
      enumSelectFromLoLImpl(lol, 0, i, list_selection, output, op);
  }

  void enumSelectFromListImpl(ExprVector& list, int start, unsigned k, ExprVector& selection, ExprVector& output, int op){
    if (k == 0){
      output.push_back(combineListExpr(selection, op));
      return;
    }
    for (int i = start; i <= list.size() - k; ++i) {
      selection.push_back(list[i]);
      enumSelectFromListImpl(list, i+1, k-1, selection, output, op);
      selection.pop_back();
    }
  }

  void enumSelectKFromList(ExprVector& list, unsigned k, ExprVector& output, int op) {
    ExprVector selection;
    for (int i = 1; i <= k; i++)
      enumSelectFromListImpl(list, 0, i, selection, output, op);
  }

  inline void invSynth(int argc, char** argv){
    static struct option long_options[] = {
        {"chc-file",    required_argument, NULL,  'F'},
        {"grammar-file", required_argument, NULL, 'G'},
        {"ctrl-state",  required_argument, NULL,  'S'},
        {"ctrl-input",  required_argument, NULL,  'I'},
        {"ctrl-output", required_argument, NULL,  'O'},
        {"data-input",  required_argument, NULL,  'i'},
        {"data-output", required_argument, NULL,  'o'},

        {"const-bw",    required_argument, NULL,  'B'},
        {"ante-size",   required_argument, NULL,  'A'},
        {"conseq-size", required_argument, NULL,  'C'},
        {"conseq-disj", required_argument, NULL,  'D'},
        // {"timeout", required_argument, NULL, 'O'},
        // {"candidates", required_argument, NULL, 'C'},
        // {"verbose", required_argument,  NULL,  'V'},
        {0,         0,                 0,  0 }
      };
    int c;
    string CSnames, CInames, COnames, DInames, DOnames;
    
    unsigned BW_bound = 2;
    int ANTE_Size = 1;
    int CONSEQ_ConjSize = 2;
    int CONSEQ_DisjSize = 1;

    char* chcfile, gfile;
    while(1) {
      int opt_idx;
      c = getopt_long(argc, argv, "S:I:O:i:o:B:A:C:D:", long_options, &opt_idx);
      if (c == -1) break; // done

      switch(c){
        case 0: 
          break;
        case 'F':
          chcfile = optarg;
          break;
        case 'G':
          gfile = optarg;
          break;
        case 'S':
          CSnames = optarg;
          break;
        case 'I':
          CInames = optarg;
          break;
        case 'O':
          COnames = optarg;
          break;
        case 'i':
          DInames = optarg;
          break;
        case 'o':
          DOnames = optarg;
          break;
        case 'B':
          BW_bound = atoi(optarg);
          break;
        case 'A':
          ANTE_Size = atoi(optarg);
          break;
        case 'C':
          CONSEQ_ConjSize = atoi(optarg);
          break;
        case 'D':
          CONSEQ_DisjSize = atoi(optarg);
          break;

        case '?':
          break; // error
        default:
          assert(0 && "bad arg");
      }
    }


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

    ExprVector cands;

    ExprVector CSvars, CIvars, COvars, DIvars, DOvars;

    for (auto & a: tr->srcVars)
    {
      if (!bv::is_bvconst(a)) continue;

      std::stringstream sbuf;
      sbuf << *qr->origNames[a];
      string vlgName = sbuf.str();
      cout<<"VAR NAME: "<<*a<<" ORIGNAL NAME: "<<*qr->origNames[a];
      
      if (CSnames.find(vlgName) != -1) {
        CSvars.push_back(a);
        cout<<" CTRL-STATE";
      }
      if (CInames.find(vlgName) != -1) {
        CIvars.push_back(a);
        cout<<" CTRL-IN";
      }
      if (COnames.find(vlgName) != -1) {
        COvars.push_back(a);
        cout<<" CTRL-OUT";
      }
      if (DInames.find(vlgName) != -1) {
        DIvars.push_back(a);
        cout<<" DATA-IN";
      }
      if (DOnames.find(vlgName) != -1) {
        DOvars.push_back(a);
        cout<<" DATA-OUT";
      }
      cout<<"\n";
    }


    vector<ExprVector> CSpredList; // {cs1: [cs1=0, cs1=1 , cs1=2 ...], cs2: [cs2=0, cs2=1 ...]}
    enumConstPredForEachVar(CSvars, BW_bound, CSpredList);
    enumConstPredForEachVar(CIvars, BW_bound, CSpredList);


    ExprVector Ante;
    enumSelectKFromListofList(CSpredList, ANTE_Size, Ante, OP_CONJ);

    int cnt = 0;
    for (Expr e : Ante){
      cnt++;
      cout<<"Enumerated Ante #"<<cnt<<" :"<<cc.printExpr(e)<<"\n";
    }


    ExprVector Conseq;
    ExprVector DataConj;

    vector<ExprVector> DpredList;

    enumConstPredForEachVar(COvars, BW_bound, DpredList);
    enumDataPredForEachVar(DOvars, BW_bound, DIvars, DpredList);

    enumSelectKFromListofList(DpredList, CONSEQ_ConjSize, DataConj, OP_CONJ);


    cnt = 0;
    for (Expr e : DataConj){
      cnt++;
      cout<<"Enumerated Dconj #"<<cnt<<" :"<<cc.printExpr(e)<<"\n";
    }

    enumSelectKFromList(DataConj, CONSEQ_DisjSize, Conseq, OP_DISJ);


    // cnt = 0;
    // for (Expr e : Conseq){
    //   cnt++;
    //   cout<<"Enumerated Conseq #"<<cnt<<" :"<<cc.printExpr(e)<<"\n";
    // }

    for (Expr a : Ante)
      for (Expr b: Conseq)
        cands.push_back(mk<IMPL>(a, b));

    cout<<"=== TOTAL candidates: "<<cands.size()<<"\n";
    // return;

    int iter = 0;
    for (auto & cand : cands)
    {
      iter++;
      cout<<"Testing Candidate: "<<cc.printExpr(cand)<<"\n";
      if (cc.checkInitiation(cand) &&
          cc.checkInductiveness(cand) &&
          cc.checkSafety())
      {
        outs () << "proved\n";
        outs () << "iter: " << iter << " / " << cands.size() << "\n";
        cc.serializeInvars();
        return;
      }
    }
    outs () << "unknown\n";

  }
  /*
  inline void simpleCheck(const char * chcfile, unsigned bw_bound, unsigned bval_bound, bool enable_eqs, bool enable_adds, bool enable_bvnot, bool enable_extract, bool enable_concr, bool enable_concr_impl, bool enable_or,
    bool enable_concr_impl_or, bool keep_dot_name_only, bool enable_inequality,
    bool enable_simplify_imply_or, const std::string & set_module_name,
    bool enable_conj_imply_concr, bool enable_conj_imply_disj, const std::set<std::string> & variable_name_set)
  {

    if (!enable_eqs) // currently, `enable_adds` and `enable_extract` depend on `enable_eqs`
    {
      enable_adds = 0;
      enable_extract = 0;
    }

    outs () << "Max bitwidth considered: " << bw_bound << "\n"
            << "Max concrete values considered: " << bval_bound << "\n"
            << "Equalities (between variables) enabled: " << enable_eqs << "\n"
            << "Bitwise additions enabled: " << enable_adds << "\n"
            << "Bitwise negations enabled: " << enable_bvnot << "\n"
            << "Inequality: " << enable_inequality << "\n"
            << "Bit extraction enabled (in equalities): " << enable_extract << "\n"
            << "Concrete values enabled (in equalities): " << enable_concr << "\n"
            << "Implications using equalities and concrete values enabled: " << enable_concr_impl << "\n"
            << "Disjunctions among (subsets of) various equalities enabled: " << enable_or << "\n"
            << "Implications using disjunctions of equalities and concrete values enabled: " << enable_concr_impl_or << "\n"
            << "Simplification of implications using disjunctions of equalities and concrete values enabled: " << enable_simplify_imply_or << "\n"
            << "Filter variable names with dot: " << keep_dot_name_only << "\n"
            << "Only keep variable names under module: " << (set_module_name.empty() ? "(none)" : set_module_name  )<< "\n"
            << "Restricting variables to be in a set of size : " << (variable_name_set.empty() ? "(none)" :  std::to_string(variable_name_set.size())  )<< "\n"
            << "(v == v/c && v == c) --> (v == c) : " << enable_conj_imply_concr << "\n"
            << "(v == v/c && v == c) --> (v == v/c || v == c)) : " << enable_conj_imply_disj << "\n"
            ;





    std::set<std::string> ctrl_state;
    std::set<std::string> ctrl_input;
    std::set<std::string> ctrl_output;
    std::set<std::string> data_input;
    std::set<std::string> data_output;

    std::ifstream fin("varlist.txt");
    if (!fin.is_open()) {
      return false;
    }

    std::string line;
    while(getline(fin,line)) {
      std::string varname, tag;
      size_t pos = line.find(' ');
      if (pos != std::string::npos){
        varname = "S_" + line.substr(0, pos);
        tag = line.substr(pos+1);
      }
      else{
        outs () << "ERROR in varlist\n";
      }
      if (tag == "CTRL_STATE"){
        ctrl_state.insert(varname);
      }
      else if (tag == "CTRL_IN"){
        ctrl_input.insert(varname);
      }
      else if (tag == "CTRL_OUT"){
        ctrl_output.insert(varname);
      }
      else if (tag == "DATA_IN"){
        data_input.insert(varname);
      }
      else if (tag == "DATA_OUT"){
        data_output.insert(varname);
      }
    }

    

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

    // get inv vars
    map<int, ExprVector> bvVars;
    map<int, Expr> bitwidths;
    set<int> bitwidths_int;

    ExprVector ctrl_state_vars;
    ExprVector ctrl_input_vars;
    ExprVector ctrl_output_vars;
    ExprVector data_input_vars;
    ExprVector data_output_vars;

    for (auto & a: tr->srcVars)
    {
      if (bv::is_bvconst(a))
      {
        if(keep_dot_name_only || !set_module_name.empty()) { // check name
          std::stringstream sbuf;
          sbuf << *qr->origNames[a];
          const std::string & state_name = sbuf.str();
          if (state_name.find(".") == std::string::npos)
            continue; // ignore those that do not contain dot
          if (!set_module_name.empty() && state_name.find("S_" + set_module_name+".") != 0)
            continue;
          if ( !variable_name_set.empty() && variable_name_set.find(state_name) == variable_name_set.end() )
            continue;
        }
        if (ctrl_state.find(state_name) != ctrl_state.end())
          ctrl_state_vars.push_back(a);
        else if (ctrl_input.find(state_name) != ctrl_input.end())
          ctrl_input_vars.push_back(a);
        else if (ctrl_output.find(state_name) != ctrl_output.end())
          ctrl_output_vars.push_back(a);
        else if (data_input.find(state_name) != data_input.end())
          data_input_vars.push_back(a);
        else if (data_output.find(state_name) != data_output.end())
          data_output_vars.push_back(a);

        unsigned bw = bv::width(a->first()->arg(1));
        bitwidths_int.insert(bw);
        bitwidths[bw] = a->first()->arg(1);
        bvVars[bw].push_back(a);
      }
    }

    ExprVector

    ExprVector eqs1;
    ExprVector eqs2;

    if (enable_eqs)
    {
      for (int i : bitwidths_int)
      {
        if (i > bw_bound) continue; // limit
        for (int j = 0; j < bvVars[i].size(); j++)
        {
          for (int k = j + 1; k < bvVars[i].size(); k++)
          {
            Expr tmp = mk<EQ>(bvVars[i][j], bvVars[i][k]);
            eqs1.push_back(tmp);
            if(enable_inequality)
              eqs1.push_back(mk<NEQ>(bvVars[i][j], bvVars[i][k]));
            if (enable_bvnot)
            {
              eqs1.push_back(tmp);
              eqs1.push_back(mk<EQ>(bvVars[i][j], mk<BNOT>(bvVars[i][k])));
            }
            if (enable_adds)
            {
              for (int l = 0; l < bvVars[i].size(); l++)
              {
                if (l == k || l == j) continue;
                Expr tmp = mk<EQ>(bvVars[i][l], mk<BADD>(bvVars[i][j], bvVars[i][k]));
                eqs1.push_back(tmp);
              }
            }
          }
          if (enable_extract)
          {
            for (int i1 = i + 1; i1 <= bw_bound; i1++)
            {
              for (int j1 = 0; j1 < bvVars[i1].size(); j1++)
              {
                eqs1.push_back(mk<EQ>(bvVars[i][j], bv::extract(i-1, 0, bvVars[i1][j1])));
              }
            }
          }
        }
      }
    }

    if (enable_concr || enable_concr_impl)
    {
      for (int i : bitwidths_int)
      {
        if (i > bw_bound) continue; // limit
        for (auto & a : bvVars[i])
        {
          for (int j = 0; j <= bval_bound && j < pow(2, i); j++)
          {
            Expr tmp = bv::bvnum(j, bv::width(bitwidths[i]), efac);
            eqs2.push_back(mk<EQ>(a, tmp));
            if(enable_inequality)
              eqs2.push_back(mk<NEQ>(a,tmp));
            if (enable_bvnot)
              eqs2.push_back(mk<EQ>(mk<BNOT>(a), tmp));
          }
        }
      }

      if (enable_concr_impl)
        for (auto & a : eqs2)
          for (auto & b : eqs2)
            if (a->left() != b->left())
              cands.insert(mk<IMPL>(a, b));

    }

    ExprVector eqsOr;
    if (enable_or || enable_concr_impl_or || enable_conj_imply_disj) {
      for (auto & c : eqs1)
        for (auto & d : eqs2)
          if (c != d) {
            eqsOr.push_back(mk<OR>(c, d));
            if (enable_or) // otherwise, we are just providing pieces
              cands.insert(mk<OR>(c, d));
          }
      
      for (auto & c : eqs2)
        for (auto & d : eqs2)
          if (c != d) {
            eqsOr.push_back(mk<OR>(c, d));
            if (enable_or) // otherwise, we are just providing pieces
              cands.insert(mk<OR>(c, d));
          }

      ExprVector eqsOrImply;
      if (enable_concr_impl_or) {
        for (auto & v_c : eqs2 )
          for (auto & v_v_or_vc : eqsOr ) {
            auto impl_cd = mk<IMPL>(v_c, v_v_or_vc);
            if ( enable_simplify_imply_or && cc.isSimplifyToConst(impl_cd) )
              continue;
            cands.insert(mk<IMPL>(v_c, v_v_or_vc));
            eqsOrImply.push_back(mk<IMPL>(v_c, v_v_or_vc));
          }
      }
    }

    ExprVector eqsAnd;
    if (enable_conj_imply_concr || enable_conj_imply_disj){
      // preparation steps 
      for (auto & c : eqs1)
        for (auto & d : eqs2)
          if (c != d) {
            eqsAnd.push_back(mk<AND>(c, d));
          }
      
      for (auto & c : eqs2)
        for (auto & d : eqs2)
          if (c != d) {
            eqsAnd.push_back(mk<AND>(c, d));
          }

      if (enable_conj_imply_concr) // otherwise we just don't insert
        for (auto & precond : eqsAnd)
          for (auto & c : eqs2) {
            cands.insert(mk<IMPL>(precond, c));
          }
    }

    if (enable_or && enable_conj_imply_concr && enable_conj_imply_disj) {
      for (auto & precond : eqsAnd)
        for (auto & poscond : eqsOr) {
          cands.insert(mk<IMPL>(precond, poscond));
        }
    }

    if (cands.empty())
    {
      cands.insert(eqs1.begin(), eqs1.end());
      cands.insert(eqs2.begin(), eqs2.end());
    }

    int iter = 0;
    for (auto & cand : cands)
    {
      iter++;
      if (cc.checkInitiation(cand) &&
          cc.checkInductiveness(cand) &&
          cc.checkSafety())
      {
        outs () << "proved\n";
        outs () << "iter: " << iter << " / " << cands.size() << "\n";
        cc.serializeInvars();
        return;
      }
    }
    outs () << "unknown\n";
  }*/
}

#endif
