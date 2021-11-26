/****************************************************************************
  FileName     [ sat.h ]
  PackageName  [ sat ]
  Synopsis     [ Define miniSat solver interface functions ]
  Author       [ Chung-Yang (Ric) Huang, Cheng-Yin Wu ]
  Copyright    [ Copyleft(c) 2010-present LaDs(III), GIEE, NTU, Taiwan ]
****************************************************************************/

#ifndef SAT_H
#define SAT_H

#include <cassert>
#include <iostream>
#include "Solver.h"

using namespace std;

/********** MiniSAT_Solver **********/
class SatSolver
{
   public : 
      SatSolver():_solver(0) { }
      ~SatSolver() { if (_solver) delete _solver; }

      // Solver initialization and reset
      void initialize() {
         reset();
         if (_curVar == 0) { _solver->newVar(); ++_curVar; }
      }
      void reset() {
         if (_solver) delete _solver;
         _solver = new Solver();
         _assump.clear(); _curVar = 0;
      }

      // Constructing proof model
      // Return the Var ID of the new Var
      inline Var newVar() { _solver->newVar(); return _curVar++; }
      // fa/fb = true if it is inverted
      void addAigCNF(Var vf, Var va, bool fa, Var vb, bool fb) {
         vec<Lit> lits;
         Lit lf = Lit(vf);
         Lit la = fa? ~Lit(va): Lit(va);
         Lit lb = fb? ~Lit(vb): Lit(vb);
         lits.push(la); lits.push(~lf);
         _solver->addClause(lits); lits.clear();
         lits.push(lb); lits.push(~lf);
         _solver->addClause(lits); lits.clear();
         lits.push(~la); lits.push(~lb); lits.push(lf);
         _solver->addClause(lits); lits.clear();
      }
      void addIffCNF(Var va, bool fa, Var vb, bool fb){
        vec<Lit> lits;
        Lit la = fa? ~Lit(va): Lit(va);
        Lit lb = fb? ~Lit(vb): Lit(vb);
        lits.push(la); lits.push(~lb);
        _solver->addClause(lits); lits.clear();
        lits.push(~la); lits.push(lb);
        _solver->addClause(lits); lits.clear();
      }
      Var And2CNF(vector<Var> varList,vector<bool> boolList){
        if (varList.size()==2){
          Var k = newVar();
          addAigCNF(k, varList[0], ~boolList[0], varList[1], ~boolList[1]);
          return k;
        } else if (varList.size()==1){
          Var k = newVar();
          addIffCNF(k,false,varList[0],~boolList[0]);
          return k;
        } else {
          vector<Var> varList1(varList.begin(),varList.begin()+varList.size()/2);
          vector<Var> varList2(varList.begin()+varList.size()/2,varList.end());
          vector<bool> boolList1(boolList.begin(),boolList.begin()+boolList.size()/2);
          vector<bool> boolList2(boolList.begin()+boolList.size()/2,boolList.end());
          Var k = And2CNF(varList1,boolList1);
          Var l = And2CNF(varList2,boolList2);
          Var m = newVar();
          addAigCNF(m,k,false,l,false);
          return m;
        }
      }
      Var Or2CNF(vector<Var> varList,vector<bool> boolList){
        if (varList.size()==2){
          Var k = newVar();
          addOrCNF(k,varList[0],~boolList[0],varList[1],~varList[1]);
          return k;
        } else if (varList.size() == 1){
          Var k = newVar();
          addIffCNF(k, false, varList[0], ~boolList[0]);
          return k;
        } else {
          vector<Var> varList1(varList.begin(),varList.begin()+varList.size()/2);
          vector<Var> varList2(varList.begin()+varList.size()/2,varList.end());
          vector<bool> boolList1(boolList.begin(),boolList.begin()+boolList.size()/2);
          vector<bool> boolList2(boolList.begin()+boolList.size()/2,boolList.end());
          Var k = Or2CNF(varList1,boolList1);
          Var l = Or2CNF(varList2,boolList2);
          Var m = newVar();
          addOrCNF(m,k,false,l,false);
          return m;
        }
      }
      // fa/fb = true if it is inverted
      void addXorCNF(Var vf, Var va, bool fa, Var vb, bool fb) {
         vec<Lit> lits;
         Lit lf = Lit(vf);
         Lit la = fa? ~Lit(va): Lit(va);
         Lit lb = fb? ~Lit(vb): Lit(vb);
         lits.push(~la); lits.push( lb); lits.push( lf);
         _solver->addClause(lits); lits.clear();
         lits.push( la); lits.push(~lb); lits.push( lf);
         _solver->addClause(lits); lits.clear();
         lits.push( la); lits.push( lb); lits.push(~lf);
         _solver->addClause(lits); lits.clear();
         lits.push(~la); lits.push(~lb); lits.push(~lf);
         _solver->addClause(lits); lits.clear();
      }
      void addOrCNF(Var vf, Var va, bool fa, Var vb, bool fb){
        vec<Lit> lits;
        Lit lf = Lit(vf);
        Lit la = fa? ~Lit(va): Lit(va);
        Lit lb = fb? ~Lit(vb): Lit(vb);
        lits.push(~la); lits.push(lf); 
        _solver->addClause(lits); lits.clear();
        lits.push(~lb); lits.push(lf);
        _solver->addClause(lits); lits.clear();
        lits.push( la); lits.push( lb); lits.push(~lf);
        _solver->addClause(lits); lits.clear();        
      }
      void addClause(const vector<Var>& varList,const vector<bool>& boolList){
        vec<Lit> lits;
        if (varList.size() != boolList.size()){
          cout<<varList.size()<<" "<<boolList.size()<<endl;
          return;
        }
        for (int i =0; i < varList.size();i++){
          Lit la = boolList[i]? Lit(varList[i]): ~Lit(varList[i]);
          lits.push(la);    
        }
        _solver->addClause(lits); lits.clear();
      }
      void assumeRelease() { _assump.clear(); }
      void assumeProperty(Var prop, bool val) {
         _assump.push(val? Lit(prop): ~Lit(prop));
      }
      bool assumpSolve() { return _solver->solve(_assump); }

      // For one time proof, use "solve"
      void assertProperty(Var prop, bool val) {
         _solver->addUnit(val? Lit(prop): ~Lit(prop));
      }
      bool solve() { _solver->solve(); return _solver->okay(); }

      // Functions about Reporting
      // Return 1/0/-1; -1 means unknown value
      int getValue(Var v) const {
         return (_solver->modelValue(v)==l_True?1:
                (_solver->modelValue(v)==l_False?0:-1)); }
      void printStats() const { const_cast<Solver*>(_solver)->printStats(); }

   private : 
      Solver           *_solver;    // Pointer to a Minisat solver
      Var               _curVar;    // Variable currently
      vec<Lit>          _assump;    // Assumption List for assumption solve
};

#endif  // SAT_H

