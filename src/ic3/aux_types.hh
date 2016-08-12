/******************************************************

Module: Auxiliary types

Author: Eugene Goldberg, eu.goldberg@gmail.com

******************************************************/
typedef std::pair<CUBE,int> StatePair;
typedef std::pair<int,int> LenInd;
typedef std::pair<float,int> ActInd;
typedef Minisat::vec<Minisat::Lit> TrivMclause;
typedef Minisat::Lit Mlit;
typedef TrivMclause MvecLits;
typedef Minisat::Clause ComplMclause;
typedef Minisat::lbool Mbool;
typedef Minisat::vec<Mbool> MboolVec;
const Mbool Mtrue = Minisat::l_True;
const Mbool Mfalse = Minisat::l_False;
const Mbool Mundef = Minisat::l_Undef;

enum PrevOper {INIT, DELETE};
enum VarType {INP,PRES_ST,NEXT_ST,INTERN};
class compare_len {
public:
  bool operator()(const LenInd &r1,const LenInd &r2) const
  {return (r1.first < r2.first);}
};

class sel_most_act {
public:
  bool operator()(const ActInd &r1,const ActInd &r2) const
  {return (r1.first > r2.first);}
};

class sel_least_act {
public:
  bool operator()(const ActInd &r1,const ActInd &r2) const
  {return (r1.first > r2.first);}
};



//
//  hsh_tbl
//
class hsh_tbl {
public:  
  int marker;
  CUBE Table;
  bool in_use; // is used as a semafor to prevent using the same hash table by two different agents
  // functions
  void  change_marker(void);
  void hsh_init(int nelems);
  void clean();
  void add_elem(void);
  int size();
  void started_using(void);
  void done_using(void);
}; 

//
//  OblTable
//
struct OblTableElem {
  CUBE St_cb; // state cube
  CUBE Inp_assgn; // corresponding input assignment
  int tf_ind; // time frame index
  int dist; // number of transitions of states of 'St_cube' from a bad state
  int succ_ind; // index of the successor state cube in 'Obl_table'
  char st_descr; // describes the state (NEW_STATE or OLD_STATE)
};

typedef std::vector <OblTableElem> OblTable;


//
//  PrQueue
//
struct PqElem {
  int tf_ind; // time frame index
  int tbl_ind; // index of this element in 'Obl_table'
};


class pq_compare
{
public:
  bool operator() (PqElem &A, PqElem &B)
  {
    return (A.tf_ind  > B.tf_ind);
  }
};

typedef std::priority_queue<PqElem,std::vector <PqElem>, pq_compare> PrQueue;


//
//   ClauseInfo
//

struct ClauseInfo 
{  
  int  span;    // specifies the span of cube. If span = j,  F_j is the latest formula where 
  // the clause at hand is present
  unsigned active : 1; // is set to 0 if clause C=F[curr_ind] is strictly subsumed by a clause
                       // obtained after pushing clause C to the next time frame
  unsigned skip : 1; // if set to 1, this clause should be ignored when pushing clauses forward
  unsigned delay : 1; // if set to 1, this clause should be ingored until the time frame where it
                      // is boundary
};


//
//   SatSolver
//

struct SatSolver
{ 
  std::string Name; // name of the SAT-solver
  Minisat::Solver *Mst; // an instance of Minisat
  int tot_num_calls; // total number of times 'Mst' is called
  int num_calls; // number of calls since the last 'init_sat_solver' operation
  int init_num_vars;  // the initial number of variables
  int num_rel_vars; // number of released vars
  PrevOper prev_oper; // specifies the previous operation
};

//
//   TimeFrame
//


struct TimeFrame
{

  SatSolver Slvr; // a copy of Minisat
  CUBE Clauses; // specifies the clauses of the current time frame
  // some clauses listed in 'Tf_cls' may be inactive
  int num_bnd_cls; // specifies number of boundary clauses of the current time frame

  int num_pbss; // number of Pre-Bad_States (states that are one transition away from a bad state)

  int tot_num_ctis; // total number of Counterexamples-To-Induction 

  int num_rcnt_ctis; // number of Cti-s generated in the current time frame when processing the latest
                     // time frame
  
 
};


typedef std::map<CLAUSE,int> ClauseTable;
typedef std::map<std::string,int> NameTable;
