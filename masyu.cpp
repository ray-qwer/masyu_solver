#include <iostream>
#include <vector>
#include <map>
#include "sat.h"
#include <fstream>
#include "string.h"
using namespace std;
// file input or manual input
// usage: ./masyu <-f/-m> <filename, if file input>
// 5 5 // height width
// .....
// w.b..
// ..w.w
// .....
// b...b
// output scheme: T/F (if the puzzle has solution), solution
// eg.
// True
// 1    .###.
//      #   #
// 2    w   .   b###.###.
//      #   #   #       #
// 3    .   .   w       w
//      #   #   #       #
// 4    .   .###.       .
//      #               #
// 5    b###.###.###.###b
class vertex{
    // how to declare id
    public:
        vertex(int i,char attr): _vid(i),_attr(attr){}
        ~vertex(){}

        void setVar(const Var& v){_var = v;}
        Var getVar() const {return _var;}
        char getAttr() const {return _attr;}
        int getVid() const {return _vid;}
    private:
        int _vid;
        Var _var;
        char _attr;
};
class line{
    // how to declare the id?
    public:
        line(int i,vertex* x,vertex* y):_lid(i){neighbor.push_back(x);neighbor.push_back(y);}
        ~line(){}
        void setVar(const Var& v){_var = v;}
        Var getVar() const {return _var;}
        int getLid() const {return _lid;}
        vector<vertex*> getNeighbor() const {return neighbor;}
    private:
        int _lid;
        Var _var;
        vector<vertex*> neighbor;
};

class masyu_puzzle{
    public:
        masyu_puzzle(){_width = 0; _height = 0;}
        masyu_puzzle(int x, int y){setDimension(x,y);}
        void setDimension(int x,int y){_height = x; _width = y;_redo=0;}
        void setPuzzle(vector<vector<char>>& puzzle){
            // vertex
            vector<vertex*> row;
            for (int i = 0; i < _height;i++){
                for (int j =0 ; j < _width; j++){
                    char attr = puzzle[i][j];
                    vertex* v = new vertex(i*_width+j,attr);
                    if (attr != '.'){
                        _candidates.push_back(v);
                    }
                    row.push_back(v);
                }
                _puzzle.push_back(row);
                row.clear();
            }
            // lines
            int linesCount = 0;
            for (int i = 0; i<_height;i++){
                for (int j=0; j< _width; j++){
                    if(i == 0 && j ==0){ continue;}
                    if (i != 0){
                        _lines.insert(pair<int,line*>(genMappingIndex(_puzzle[i-1][j]->getVid(),_puzzle[i][j]->getVid()),new line(linesCount,_puzzle[i-1][j],_puzzle[i][j])));
                        linesCount++;
                    } 
                    if (j != 0){
                        _lines.insert(pair<int,line*>(genMappingIndex(_puzzle[i][j-1]->getVid(),_puzzle[i][j]->getVid()),new line(linesCount,_puzzle[i][j-1],_puzzle[i][j])));
                        linesCount++;
                    }
                }
            }
            
        }
        bool printPuzzle(){
            if (_puzzle.size()==0){
                return false;
            }
            // print
            for (int i = 0 ; i<_height;i++){
                cout<<i<<"\t";
                for (int j = 0 ; j< _width; j++){
                    cout<<_puzzle[i][j]->getAttr();
                    if (j != _width -1){
                        if(_lines[genMappingIndex(i*_width+j,i*_width+j+1)]->getVar())
                            cout<<_lines[genMappingIndex(i*_width+j,i*_width+j+1)]->getLid();
                            // cout<"===";
                        else cout<<"   ";
                    }
                }
                cout<<"\n\t";
                if (i != _height-1){
                    for (int j = 0;j<_width; j++){
                        if (_lines[genMappingIndex(i*_width+j,(i+1)*_width+j)]->getVar())
                            cout<<_lines[genMappingIndex(i*_width+j,(i+1)*_width+j)]->getLid();                            
                            // cout<<"|"<<"   ";
                        else cout<<"    ";
                    }
                }
                cout<<endl;
            }
            return true;
        }
        bool printResultPuzzle(SatSolver& s){
            if (_puzzle.size()==0){
                return false;
            }
            // print
            cout<<"redo: "<<_redo<<endl;
            for (int i = 0 ; i<_height;i++){
                cout<<i<<"\t";
                for (int j = 0 ; j< _width; j++){
                    cout<<_puzzle[i][j]->getAttr();
                    // cout<<_puzzle[i][j]->getAttr();
                    if (j != _width -1){
                        // cout<<s.getValue(_lines[genMappingIndex(i*_width+j,i*_width+j+1)]->getVar());
                        if(s.getValue(_lines[genMappingIndex(i*_width+j,i*_width+j+1)]->getVar())){
                            cout<<"===";
                        }
                        else cout<<"   ";
                    }
                }
                cout<<"\n\t";
                if (i != _height-1){
                    for (int j = 0;j<_width; j++){
                        // cout<<s.getValue(_lines[genMappingIndex(i*_width+j,(i+1)*_width+j)]->getVar());
                        if (s.getValue(_lines[genMappingIndex(i*_width+j,(i+1)*_width+j)]->getVar()))
                            cout<<"|"<<"   ";
                        else cout<<"    ";
                    }
                }
                cout<<endl;
            }
            return true;
        }
        void genProofModel(SatSolver& s){
            // biggest problem 
            vector<Var> vertexVarList;
            for (int i = 0; i < _height; i++){
                for (int j = 0; j< _width; j++){
                    Var v = s.newVar();
                    _puzzle[i][j]->setVar(v);
                    vertexVarList.push_back(v);
                }
            }
            for(auto i = _lines.begin();i!=_lines.end();i++){
                Var v = s.newVar();
                i->second->setVar(v);
            }
            vector<bool> vertexBoolTmp;
            Var result = s.newVar();
            vector<Var> tmp;
            vertexBoolTmp.push_back(true);
            vertexBoolTmp.push_back(false);
            tmp.assign(2,result);
            for(int i = 0;i<vertexVarList.size();i++){
                tmp[0] = vertexVarList[i];
                s.addClause(tmp,vertexBoolTmp);
                // s.assumeProperty(vertexVarList[i],true);
            }
            vertexVarList.push_back(result);
            vertexBoolTmp.assign(vertexVarList.size(), false);
            vertexBoolTmp[vertexVarList.size()-1] = true;
            s.addClause(vertexVarList,vertexBoolTmp);
            s.assumeProperty(result,true);
            for (int i = 0; i < _height; i++){
                for (int j = 0; j < _width; j++ ){
                    
                    vector<Var> neighborVarList;
                    vector<bool> boolList;
                    find_line_neighbor(i,j,neighborVarList);
                    neighborVarList.push_back(_puzzle[i][j]->getVar());
                    switch(neighborVarList.size()){
                        case 3:
                            boolList.assign(3,false);
                            for(int i = 0;i<2; i++){ // one connect
                                boolList[i] = true;
                                s.addClause(neighborVarList,boolList);
                                boolList[i] = false;
                            }
                            break;
                        case 4:
                            boolList.assign(4,false);
                            s.addClause(neighborVarList,boolList); // three conntect
                            boolList.assign(4,true); // one connect
                            boolList[3] = false;
                            for(int i = 0; i<3;i++){
                                boolList[i] = false;     // 
                                s.addClause(neighborVarList,boolList);
                                boolList[i] = true;
                            }
                            break;
                        case 5:
                            boolList.assign(5,false);
                            s.addClause(neighborVarList,boolList); // four connect
                            for (int i = 0; i<4; i++){
                                boolList[i] = true; // three connnect
                                s.addClause(neighborVarList,boolList);
                                boolList[i] = false;
                            }
                            boolList.assign(5,true); // one connect
                            boolList[4]=false;
                            for (int i = 0;i<4;i++){
                                boolList[i] = false;
                                s.addClause(neighborVarList,boolList);
                                boolList[i] = true;
                            }
                            break;
                        default: 
                            // cout<<i<<" "<<j<<endl;
                            break;
                    }
                    if (_puzzle[i][j]->getAttr() != '.'){
                        // cout<<neighborVarList.size()<<endl;
                        boolList.assign(neighborVarList.size(),true); // no connect
                        boolList[boolList.size()-1] = false;
                        s.addClause(neighborVarList, boolList);
                        // imply black and white
                        // black pearl
                        if (_puzzle[i][j]->getAttr() == 'b'){
                            // constraints of itself-> corner
                            // cannot be strait: (x y-1)and(x, y+1) or (x-1 y)and(x+1 y)->v'
                            // int flag = getFlagOfVertex(i,j);
                            int vertexVar = _puzzle[i][j]->getVid();
                            vector<Var> VerticalTwoLinesCombine;
                            vector<Var> VerticalSingleElement;
                            vector<Var> HorizentalTwoLinesCombine;
                            vector<Var> HorizentalSingleElement;
                            vector<Var> tmp(3,_puzzle[i][j]->getVar());
                            boolList.assign(3,false);
                            boolList[1] = true;
                            if (vertexVar % _width >1){ // left
                                Var m = s.newVar();
                                s.addAigCNF(m,_lines[genMappingIndex(vertexVar-1,vertexVar-2)]->getVar(),false,_lines[genMappingIndex(vertexVar,vertexVar-1)]->getVar(),false);
                                tmp[0] = (_lines[genMappingIndex(vertexVar,vertexVar-1)]->getVar()); 
                                tmp[1] = (_lines[genMappingIndex(vertexVar-2,vertexVar-1)]->getVar()); 
                                s.addClause(tmp,boolList);
                                VerticalTwoLinesCombine.push_back(m);
                            }
                            if (vertexVar % _width < _width-2){
                                Var m = s.newVar();
                                s.addAigCNF(m,_lines[genMappingIndex(vertexVar+1,vertexVar+2)]->getVar(),false,_lines[genMappingIndex(vertexVar,vertexVar+1)]->getVar(),false);
                                tmp[0] = (_lines[genMappingIndex(vertexVar,vertexVar+1)]->getVar()); 
                                tmp[1] = (_lines[genMappingIndex(vertexVar+2,vertexVar+1)]->getVar()); 
                                s.addClause(tmp,boolList);
                                VerticalTwoLinesCombine.push_back(m);
                            }
                            if (vertexVar / _width > 1){
                                Var m = s.newVar();
                                s.addAigCNF(m,_lines[genMappingIndex(vertexVar-_width,vertexVar-2*_width)]->getVar(),false,_lines[genMappingIndex(vertexVar,vertexVar-_width)]->getVar(),false);
                                tmp[0] = (_lines[genMappingIndex(vertexVar,vertexVar-_width)]->getVar()); 
                                tmp[1] = (_lines[genMappingIndex(vertexVar-_width,vertexVar-2*_width)]->getVar()); 
                                s.addClause(tmp,boolList);
                                HorizentalTwoLinesCombine.push_back(m);
                            }
                            if (vertexVar / _width < _height-2){
                                Var m = s.newVar();
                                s.addAigCNF(m,_lines[genMappingIndex(vertexVar+_width,vertexVar+2*_width)]->getVar(),false,_lines[genMappingIndex(vertexVar,vertexVar+_width)]->getVar(),false);
                                tmp[0] = (_lines[genMappingIndex(vertexVar,vertexVar+_width)]->getVar()); 
                                tmp[1] = (_lines[genMappingIndex(vertexVar+_width,vertexVar+2*_width)]->getVar()); 
                                s.addClause(tmp,boolList);
                                HorizentalTwoLinesCombine.push_back(m);
                            }
                            if (HorizentalTwoLinesCombine.empty() || VerticalTwoLinesCombine.empty()){
                                s.assertProperty(_puzzle[i][j]->getVar(),false);
                                cout<<"the puzzle is too small"<<endl;
                                // break;
                                return;
                            }
                            for (auto k = HorizentalTwoLinesCombine.begin(); k != HorizentalTwoLinesCombine.end();k++){
                                for (auto l = VerticalTwoLinesCombine.begin(); l != VerticalTwoLinesCombine.end();l++){
                                    vector<Var> tmp;
                                    tmp.push_back((*k)); tmp.push_back((*l)); tmp.push_back(_puzzle[i][j]->getVar());
                                    boolList.assign(3,false);
                                    boolList[2] = true;
                                    s.addClause(tmp,boolList);
                                }
                            }
                            if (vertexVar % _width == 1) s.assertProperty(_lines[genMappingIndex(vertexVar,vertexVar-1)]->getVar(),false);
                            if (vertexVar % _width == _width-2) s.assertProperty(_lines[genMappingIndex(vertexVar,vertexVar+1)]->getVar(),false);
                            if (vertexVar / _width == 1) s.assertProperty(_lines[genMappingIndex(vertexVar,vertexVar-_width)]->getVar(),false);
                            if (vertexVar / _width == _height-2) s.assertProperty(_lines[genMappingIndex(vertexVar,vertexVar+_width)]->getVar(),false);
                            if (vertexVar % _width > 0) HorizentalSingleElement.push_back(_lines[genMappingIndex(vertexVar,vertexVar-1)]->getVar());
                            if (vertexVar % _width < _width-1) HorizentalSingleElement.push_back(_lines[genMappingIndex(vertexVar,vertexVar+1)]->getVar());
                            if (vertexVar / _width > 0) VerticalSingleElement.push_back(_lines[genMappingIndex(vertexVar,vertexVar-_width)]->getVar());
                            if (vertexVar / _width < _height-1) VerticalSingleElement.push_back(_lines[genMappingIndex(vertexVar,vertexVar+_width)]->getVar());
                            bool TwoDirectionSingleElement = true;
                            if (HorizentalSingleElement.size() == 2){
                                s.addOrCNF(_puzzle[i][j]->getVar(),HorizentalSingleElement[0],true,HorizentalSingleElement[1],true);
                                TwoDirectionSingleElement = false;
                            }
                            if (VerticalSingleElement.size() == 2){
                                s.addOrCNF(_puzzle[i][j]->getVar(),VerticalSingleElement[0],true,VerticalSingleElement[1],true);
                                TwoDirectionSingleElement = false;
                            }
                            if(TwoDirectionSingleElement){
                                s.addAigCNF(_puzzle[i][j]->getVar(),HorizentalSingleElement[0],false,VerticalSingleElement[0],false);
                            }
                            // if (HorizentalTwoLinesCombine.size() == 2){
                            //     s.addOrCNF(_puzzle[i][j]->getVar(),HorizentalTwoLinesCombine[0],true,HorizentalTwoLinesCombine[1],true);
                            //     TwoDirectionSingleElement = false;
                            // }
                            // if (VerticalTwoLinesCombine.size() == 2){
                            //     s.addOrCNF(_puzzle[i][j]->getVar(),VerticalTwoLinesCombine[0],true,VerticalTwoLinesCombine[1],true);
                            //     TwoDirectionSingleElement = false;
                            // }
                            // if(TwoDirectionSingleElement){
                            //     s.addAigCNF(_puzzle[i][j]->getVar(),HorizentalTwoLinesCombine[0],false,VerticalTwoLinesCombine[0],false);
                            // }

                            
                            // x y-2, x-2 y, x+2 y, x y+2
                            // bind up: (x y-2)and(x y-1) or (x-2 y)and(x-1 y) or (x+2 y)and(x+1 y) or (x y+2)and(x y+1)
                            // tired to find...

                        } // white pearl
                        else if (_puzzle[i][j]->getAttr() == 'w'){
                            int flag = getFlagOfVertex(i,j);
                            int vertexVar = _puzzle[i][j]->getVid();
                            if (flag == 0){
                                Var m = s.newVar();
                                Var n = s.newVar();
                                s.addOrCNF(_puzzle[i][j]->getVar(),m,false,n,false);
                                s.addAigCNF(m,_lines[genMappingIndex(vertexVar-1,vertexVar)]->getVar(),false,_lines[genMappingIndex(vertexVar,vertexVar+1)]->getVar(),false);
                                s.addAigCNF(n,_lines[genMappingIndex(vertexVar-_width,vertexVar)]->getVar(),false,_lines[genMappingIndex(vertexVar,vertexVar+_width)]->getVar(),false);
                                vector<Var> twoBlockAwayVertexList; // horizental constraints
                                if (vertexVar%_width > 1){
                                    twoBlockAwayVertexList.push_back(_lines[genMappingIndex(vertexVar-2,vertexVar-1)]->getVar());
                                }
                                if (vertexVar%_width < _width-2){
                                    twoBlockAwayVertexList.push_back(_lines[genMappingIndex(vertexVar+1,vertexVar+2)]->getVar());                                    
                                }
                                Var l = s.newVar();
                                if (twoBlockAwayVertexList.size()==1){
                                    // s.addIffCNF(l,false,twoBlockAwayVertexList[0],false);
                                } else if (twoBlockAwayVertexList.size()==2){
                                    s.addAigCNF(l,twoBlockAwayVertexList[0],false,twoBlockAwayVertexList[1],false);
                                }
                                boolList.assign(3,false);
                                vector<Var> tmp;
                                tmp.push_back(_puzzle[i][j]->getVar()); tmp.push_back(l); tmp.push_back(m);
                                s.addClause(tmp,boolList);
                                twoBlockAwayVertexList.clear(); 
                                tmp.clear();
                                // vertical constraints
                                if (vertexVar/_width > 1){
                                    twoBlockAwayVertexList.push_back(_lines[genMappingIndex(vertexVar-_width,vertexVar-2*_width)]->getVar());
                                }
                                if (vertexVar/_width < _height-2){
                                    twoBlockAwayVertexList.push_back(_lines[genMappingIndex(vertexVar+_width,vertexVar+2*_width)]->getVar());
                                }
                                l = s.newVar();
                                if (twoBlockAwayVertexList.size()==1){
                                    // s.addIffCNF(l,false,twoBlockAwayVertexList[0],false);
                                } else if (twoBlockAwayVertexList.size()==2){
                                    s.addAigCNF(l,twoBlockAwayVertexList[0],false,twoBlockAwayVertexList[1],false);
                                }
                                boolList.assign(3,false);
                                tmp.push_back(_puzzle[i][j]->getVar()); tmp.push_back(l); tmp.push_back(n);
                                s.addClause(tmp,boolList);

                            } 
                            else if (flag == 1 || flag == 4){ // horizental 
                                s.addAigCNF(_puzzle[i][j]->getVar(),_lines[genMappingIndex(vertexVar-1,vertexVar)]->getVar(),false,_lines[genMappingIndex(vertexVar,vertexVar+1)]->getVar(),false);
                                if (flag == 1) s.addOrCNF(_puzzle[i][j]->getVar(),_lines[genMappingIndex(vertexVar-1,vertexVar-1+_width)]->getVar(),false,_lines[genMappingIndex(vertexVar+1,vertexVar+1+_width)]->getVar(),false);
                                else s.addOrCNF(_puzzle[i][j]->getVar(),_lines[genMappingIndex(vertexVar-1-_width,vertexVar-1)]->getVar(),false,_lines[genMappingIndex(vertexVar+1-_width,vertexVar+1)]->getVar(),false);
                                
                            } else if (flag == 2 || flag == 8){ // vertical
                                s.addAigCNF(_puzzle[i][j]->getVar(),_lines[genMappingIndex(vertexVar-_width,vertexVar)]->getVar(),false,_lines[genMappingIndex(vertexVar,vertexVar+_width)]->getVar(),false);
                                if (flag == 2) s.addOrCNF(_puzzle[i][j]->getVar(),_lines[genMappingIndex(vertexVar+1-_width,vertexVar-_width)]->getVar(),false,_lines[genMappingIndex(vertexVar+_width,vertexVar+_width+1)]->getVar(),false);
                                else s.addOrCNF(_puzzle[i][j]->getVar(),_lines[genMappingIndex(vertexVar-1-_width,vertexVar-_width)]->getVar(),false,_lines[genMappingIndex(vertexVar+_width-1,vertexVar+_width)]->getVar(),false);
                            } else {
                                cout<<"unsat"<<endl;
                                boolList.assign(neighborVarList.size(),false);
                                s.addClause(neighborVarList,boolList);
                                // UNSAT
                            }
                        }
                    }
                    
                }
            }
           
        }
        bool solvePuzzle(SatSolver& s){
            bool result = s.assumpSolve();

            if (result){
                // dfs to search if it is a circle
                // cout<<"result"<<endl;
                if (_candidates.empty()) return result;
                // cout<<"run"<<endl;
                vertex* start = _candidates[0];
                int countCandidatesOfCycle = 1;
                vector<Var> cycle;
                vertex* now = start;
                vertex* prev = NULL;
                while (true){
                    vector<line*> neighbor;
                    find_line_neighbor(now->getVid(), neighbor);
                    bool no_combine = true;
                    for (auto i = neighbor.begin(); i != neighbor.end(); i++){
                        if (s.getValue((*i)->getVar())==1){
                            vector<vertex*> n = (*i)->getNeighbor(); 
                            for (int j = 0; j<2;j++){
                                if (n[j]!=now && n[j]!=prev){
                                    prev = now;
                                    now = n[j];
                                    no_combine = false;
                                    cycle.push_back((*i)->getVar());
                                    // cout<<"here"<<endl;
                                    break;
                                }
                            }
                        }
                        if (!no_combine) break;
                    }
                    if (no_combine){
                        cout<<"impossible"<<endl;
                        return false;
                    } 
                    if (now == start){
                        // cout<<"why"<<endl;
                        if (_candidates.size() == countCandidatesOfCycle) return true;
                        else{
                            // addclause
                            // cout<<_candidates.size()<<endl;
                            // cout<<countCandidatesOfCycle<<endl;
                            vector<bool> boolList(cycle.size(),false);
                            s.addClause(cycle,boolList);
                            _redo+=1;
                            // cout<<"redo"<<endl;
                            return solvePuzzle(s);
                            // return true;
                        }
                    }else if(now->getAttr() !='.') countCandidatesOfCycle+=1;
                }
            }
            return result;
        }
    private:
        int _redo;
        int _width;
        int _height;
        vector<vector<vertex*>> _puzzle;
        vector<vertex*> _candidates;
        map<int, line*> _lines;   // pair<int,int> are the pair of index of vertexex, smaller at front
        int genMappingIndex(int front,int back){ if(front >back) return (back<<16)+front; else return (front<<16)+back;}
        int const getFlagOfVertex(int i, int j){
            int flag = 0;
            if (i == 0){flag += 1;}
            if (j == 0){flag += 2;}
            if (i == _height-1){flag += 4;}
            if (j == _width-1){flag += 8;}
            return flag;
        }
        void const find_line_neighbor(int i,int j,vector<line*>& varList){
            find_line_neighbor(i*_width+j,varList);
        }
        void const find_line_neighbor(int vertexVar, vector<line*>& varList){
            if (vertexVar % _width > 0){
                varList.push_back(_lines[genMappingIndex(vertexVar,vertexVar - 1)]);
            }
            if (vertexVar % _width < _width-1){
                varList.push_back(_lines[genMappingIndex(vertexVar,vertexVar+1)]);
            }
            if (vertexVar / _width > 0 ){
                varList.push_back(_lines[genMappingIndex(vertexVar-_width,vertexVar)]);
            }
            if (vertexVar / _width < _height-1){
                varList.push_back(_lines[genMappingIndex(vertexVar+_width,vertexVar)]);
            }
            return;
        }
        void const find_line_neighbor(int i, int j, vector<Var>& varList){
            find_line_neighbor(i*_width+j,varList);
        }
        void   const find_line_neighbor(int vertexVar,vector<Var>& varList){
            // int flag = getFlagOfVertex(i,j);            
            // before sleep segmentation fault here
            // int vertexVar = i*_width+j;
            if (vertexVar % _width > 0){
                varList.push_back(_lines[genMappingIndex(vertexVar,vertexVar - 1)]->getVar());
            }
            if (vertexVar % _width < _width-1){
                varList.push_back(_lines[genMappingIndex(vertexVar,vertexVar+1)]->getVar());
            }
            if (vertexVar / _width > 0 ){
                varList.push_back(_lines[genMappingIndex(vertexVar-_width,vertexVar)]->getVar());
            }
            if (vertexVar / _width < _height-1){
                varList.push_back(_lines[genMappingIndex(vertexVar+_width,vertexVar)]->getVar());
            }
            return;
        }
};

int main(int argc,char* argv[]){
    bool flag_file_or_manual = true;
    if (argc > 3){
        cerr<<"Too many variables"<<endl;
        exit(1);
    }else if(argc <2){
        cerr <<"Too few variables"<<endl;
        exit(1);
    }

    int height;
    int width;
    masyu_puzzle ms;
    if (!strcmp(argv[1],"-f") || !strcmp(argv[1],"-F")){
        cout<<"input from file"<<endl;
        flag_file_or_manual = true;
        ifstream file;
        file.open(argv[2]);
        if(!file){
            cerr<<"cannot find file."<<endl;
            return 0;
        }
        // read puzzle content
        int file_row_count = 0;
        string s;
        vector<vector<char>> puzzle;
        while(file){
            getline(file,s);
            if (file_row_count == 0){
                int pilot = s.find(" ");
                height = stoi(s.substr(0,pilot));
                width = stoi(s.substr(pilot,s.length()-1));
                ms.setDimension(height,width);
                // allocate space for 2d vector
                vector<char> row(width,0);
                puzzle.assign(height,row);
            }
            else if (file_row_count <= height){
                for(int i = 0; i< width;i++){
                    puzzle[file_row_count-1][i] = s[i];
                    // confirm that perform well
                }
            }
            file_row_count += 1;
        }
        ms.setPuzzle(puzzle);


    }else if (!strcmp(argv[1],"-m")||!strcmp(argv[1],"-M")){
        flag_file_or_manual = false;
        cout<<"input from manually key in"<<endl;
        string s;
        cin>>s;
        height = stoi(s);
        cin>>s;
        width = stoi(s);
        ms.setDimension(height,width);
        vector<char> row(width,0);
        vector<vector<char>> puzzle(height,row);
        for(int i = 0; i < height; i++){
            cin>>s;
            for (int j = 0; j < width; j++){
                puzzle[i][j] = s[i];
            }
        }
        ms.setPuzzle(puzzle);
    }
    SatSolver solver;
    solver.initialize();
    // genProofModel
    ms.genProofModel(solver);
    // ms.printPuzzle();
    bool result = ms.solvePuzzle(solver);
    solver.printStats();
    cout << (result? "SAT" : "UNSAT") << endl;
    if (result) ms.printResultPuzzle(solver);
}