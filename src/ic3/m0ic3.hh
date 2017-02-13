/******************************************************

Module: IC3 types

Author: Eugene Goldberg, eu.goldberg@gmail.com

******************************************************/
#include "aux_types.hh"

extern int debug_flag;
/*================================

  C L A S S   C O M P _ I N F O

=================================*/
class CompInfo
{
public:

  
  Circuit *N; // circuit whose safety proprety is to be checked
  CUBE Ordering; // Ordering[i] specifies the order of a gate used to
                 // generate CNF formulas. For every input gate and latch
                 // Ordering[i] == i
 
  int prop_ind; // specifies the index of the property to be checked 
                // to be implemented for the integrated version
   
  CUBE Gate_to_var; // gate_to_var[gate_ind] gives the variable assigned to 
                    // the output of gate 'gate_ind'
 
  int num_circ_vars; // number of variables assigned to gates of N

  CUBE Pres_svars; // array specifying the current state variables
  CUBE Next_svars; // array specifying the next state variables
  DNF Coi_svars; // Coi_svars[i] spec. the vars that are in the cone influence
                // in the time frame that is 'i' trans. away from a bad state
  
  CUBE Inp_vars; // array specifying the list of input variables

  // constr related

  ConstrNames Cgate_names; // Stores the names of constrained gates listed in 'file.cnstr'
                        // Cgate_names["gate_name"] specifies gate polarity (1 means negation)
  SCUBE Init_clits; // Stores the constrained literals of the Verilog description

// Constr_gates specify constrained literals in terms of 
// gates of circuit N. Constr_gates[gate_ind] == 0 (respectively 1) corresponds
// to the positive (respectively negative) literal of the variable 'gate_ind+1'

  ConstrGates Constr_gates; 

// specify constrained input literals  in terms of vars 
// of circuit N i.e. combinational input and present state variables 
  CUBE Constr_ilits; 

// 'Constr_nilits' specify constrained literals that are not input ones
// in terms of N i.e. combinational internal and next state variables. 
// For ever present state variable listed in 'Constr_ilits', the corresponding 
// next state variable is added to 'Constr_nilits'

  SCUBE Constr_nilits; 

  CUBE Fun_coi_lits; // lists literals of 'Constr_nilits' that are in the coi
                     //  of the property

  CUBE Tr_coi_lits; // lists literals of 'Constr_nilits' that are in the coi
                    //  of the transitive relation

  bool vac_true; // set to 'true', if the init. states do not sat. the constr.
                 // in this case, the property is vacuously true
  
  SCUBE Constr_ps_lits;//spec. constr. pres. state lits 
                       // (used when lift. a state)
  SCUBE Constr_inp_lits; // specifies constrained input lits

  bool constr_flag; // if 'constr_flag == true', then 'ic3' is run with option
                    // --constr

  CNF Prop; // property (expressed in terms of present state variables)
  int num_prop_vars; // number of variables in 'Prop'

  CNF Short_prop; // property without clauses shared with the transition 
                  // relation

  CNF Simp_PrTr; //  Prop/Short_prop plus Tr after simplfication
  int max_num_vars0; // max(max(num_ist_vars,num_bst_vars),num_tr_var)
  int max_num_vars; // max_num_vars0 plus variables that take into account 
                    // that property is specified in terms of present and
                    // next state variables

  int max_pres_svar; // specifies the largest present state variable

  CUBE Next_to_pres; // Next_pres[i] equals  the  index of the present state
  // variable corresponding to next state variable 'i'
  // if 'i' is not a state variable Next_pres[i] = -1
  CUBE Pres_to_next; // Pres_next[i] equals  the  index of the next state 
                     // variable corresponding to present state variable 'i'
                     // if 'i' is not a state variable Next_pres[i] = -1

  

  // Used in convertion of verilog description to gates

  SCUBE Inps; // Stores literals specifying inputs
  SCUBE Lats; // Stores literals specifying latches
  SCUBE Invs; // Stores literals specifying additional invertors
  int const_flags; // is used to record the info on whether constant 0 or 1 
                   //have been used


  //--------------- basic data

  CNF F; // set of all inductive cubes

  DNF Flits0; // 'Flits0' specifies clauses of F (in terms of indexes of F) that 
                 // contain the negative literal of 'i+1'

  DNF Flits1; // the same as 'Flits0' but for positive literals


  FltCube Lit_act0; // Lit_act0[i] describes the presence of the negative 
                    //literal of variable  'i+1' in clauses of F
  FltCube Lit_act1; // Lit_act1[i] describes the presence of the positive 
                    //literal of variable  'i+1' in clauses of F

  FltCube Tmp_act0;
  FltCube Tmp_act1;


  std::vector <TimeFrame> Time_frames; // Time_frames[i] specifies data 
                                       // members of i-th time frame
  std::vector <ClauseInfo> Clause_info; // Clause_info[i] gives information
                                        // about cube F[i]

  ClauseTable Clause_table; // used to eliminate duplicates

  int tf_lind; // (lind stands for Largest IND) specifies the value of the 
               // latest time frame for which an approximation is built

  std::vector <VarInfo> Var_info; // Var_type[i] gives information about 
                                  // variable 'i+1'

  PrQueue Pr_queue; // priority queue of proof obligations
  OblTable Obl_table; // table of proof obligations

  DNF Cex; // a counterexample in terms of states extracted from 'Obl_table'


  CNF Bad_states; // bad states expressed in terms of next state variables

  int inv_ind; // specifies the index of F_i that is an invariant
               // if no invariant is found, inv_ind is equal to -1
 
  // picking literals
  float multiplier; // used to increase the value of factor
  float factor; // specifies the current increment when choosing a literal 
  float max_act_val; // if the value of 'max_act_val' is accided the value 
                     // of 'factor' is scaled down
  int max_num_elems; // used in the PART_SORT sorting mode
  

 // --------------- Parameters controlling algorithm's behavior
 
  bool print_inv_flag; // if true, the invariant found by the program 
                       // (if any) is printed out
  char print_cex_flag; // 0 - counterexample (cex) is not printed out, 
                       // 1 - cex is printed out as a text file
                       // 2 - cex is printed out as a CNF formula
  char out_file[MAX_NAME]; // the root name of the output file
  int verbose; // specifies the level details to be printed out
  int gcount_max; // specifies the maximum value of gcount 
                  // (used for debugging)
  int fin_tf; // stop after 'fin_tf' is reached (unless fin_tf < 0)
  bool print_only_ind_clauses; // print out only the part of the
                               // invariant consisting of inductive clauses
  long int excl_st_count; // number of times the exclude_state
  // procedure is called
  int time_limit; // if time_limit > 0, the program terminates when the run
                  //  time exceeds 'time_limit' seconds
  bool use_short_prop; // if true, the program uses 'Short_prop' instead of
                       // 'Prop' in the presence of clauses of 'Tr'
  int stat_data; // if stat_data > 0, some statistics is printed out, the 
                 //value of 'stat_data' specifying the level of detail
  bool selector; // used for debugging
  bool print_clauses_flag; // if true, all the clauses of F are printed out
  bool statistics; // is 'true', then statistics is printed out
  bool rem_subsumed_flag; // if 'true' subsumed clauses are removed (the 
                          // default value is false)
  int lit_pick_heur; // literal picking heuristics
  int act_upd_mode;  // value of this variable constrols how variable
                     //  activity is computed
  int sorted_objects; // specifies whether literals or variables are sorted
  int lift_sort_mode; // value of this variable controls how assumptions 
                      // are sorted when lifting a state
  int ind_cls_sort_mode; // value of this variable controls how assumptions 
                         // are sorted when looking for an inductive clause
  int gate_sort_mode; // value of this variable controls the ordering of
                      // gates of the circuit used to generate formulas
  int max_coi_depth; // the maximum number of time frames unfolded when 
                     // computing the cone of influence
  bool ctg_flag; // if 'true' generalization based on computing counterexamples
                //  to generalization is applied
  int max_ctg_cnt; // this variable controls how many ctgs are tried to be 
                   //excluded before shortening  the current clause to be made
                   // inductive
  int max_rec_depth; // this variables how hard IC3 tries to eliminate an ctg
  int grl_heur; // controls whether joins are used in the generalization 
                // procedure when 'ctg_flag == false'

  int num_tr_vars; // number of variables in 'Tr'
  int num_ist_vars; // number of variables in 'Ist'
 
 
  
 

  // ------------- Debugging
  CUBE Glob_lits; 
  
  //
  // public methods
  //

  int run_ic3();
  int mic3();
  void init_parameters();
  void print_header();
  void blif_format_model(char *fname); 
  bool check_init_states();
  void assign_var_type();
  void assign_value();
  void print_invariant(bool only_new_clauses);
  void print_fclauses();
  bool ver_trans_inv();
  void form_cex();
  void fprint_cex1();
  void fprint_cex2();
  bool ver_cex();
  void print_stat();
  void find_file_format(char *fname);
  void order_gates();
  //  
  // Sat-solver related
  //
  void init_sat_solver(SatSolver &S,int nvars,std::string &Id_name);
  void delete_solver(SatSolver &Slvr);
  void accept_new_clause(SatSolver &Slvr,CLAUSE &C);
  void accept_new_clauses(SatSolver &Slvr,CNF &H);
  // 
  //  to bridge ic3 and ebmc

  void gen_cnfs(char *fname,bool print_flag);
  void build_arrays();
  void form_max_pres_svar();
  void form_var_nums();
  int upd_gate_constr_tbl(int lit,int gate_ind);
  void start_new_gate(CUBE &Gate_inds,Circuit *N,CDNF &Pin_names);
  void form_gate_fun(Circuit *N,int gate_ind,CUBE &Pol);
  void form_consts(Circuit *N);
  void form_constr_lits();
  void add_constrs();

protected:

// ------------------ Statistics

  int num_bstate_cubes; // number of times a bad state has been lifted
  float length_bstate_cubes;  // number of lengths of the bad state cubes 
                              // after lifting
  int num_gstate_cubes; // number of times a good state has been lifted
  float length_gstate_cubes; // number of length of the good state cubes
                             //  after lifting
  long new_state_cnt; // counts the number of new states that appeared 
                      // in the obligation table
  long old_state_cnt; // counts the number of old states that appeared 
                      // in the obligation table
  long root_state_cnt; // counts the number of root states that appeared
                       //  in the obligation table
  long tot_ctg_cnt; // total number number of CTGs, the algorithm tried to 
                    // exclude
  long succ_ctg_cnt; // the number of CTGs that was actually excluded
  long triv_old_st_cnt; // counts the number of old states that were 
                        // trivially excluded

  int max_num_tfs; // specifies the number of time frames mic3 had to use 
                   // to solve the formula
  int orig_ind_cls; // gives the total number of original inductive clauses
  int succ_impr;  // gives the total number of successful improvements of 
                    //inductive clauses
  int failed_impr; // failed improvements
  int max_num_impr; // specifies the maximum number of improvements for an
                      // inductive clause
  int num_push_clause_calls; // contains the number of sat calls to push clauses
  int num_inact_cls; // specifies the number of clauses of F that are currently
                     //  inactive
  int num_add1_cases; // number of cases where 'replce_or_add_clause' returned 
                      // ADD1
  int num_add2_cases; //                                or ADD2
  int num_restore_cases; //                             or RESTORE
  int num_replaced_cases; //                             or REPLACED


 


 // -------------- Sat-solvers


  SatSolver Gen_sat;  // A sat-solver used for miscellaneous SAT jobs
  SatSolver Bst_sat;  // A sat-solver used for finding a bad state rechable 
                      // from an F_j-state
  SatSolver Lbs_sat; // A sat-solver used for lifting a bad state
  SatSolver Lgs_sat; // A sat-solver used for lifting a good state
  SatSolver Dbg_sat; // A sat-solver used for debugging

  NameTable Name_table; // Table with the names of Sat-solvers for
                        //  which 'init_sat_solver' were invoked

 // ------------- init data

  CNF Tr; // transition relation
 

  CNF Ist; // initial states
 

 // protected methods

 #include "i5nline.hh"

 #include "m2ethods.hh"


}; /* end of class CompInfo */


void read_solution(char *fname,CUBE &Sol);
void read_conv_table(CUBE &Conv_table,char *fname,int &max_var);
void form_table(CUBE &Table1,CUBE &Table0,int max_num_vars);
void array_to_set(SCUBE &A,CUBE &B);
bool all_elems_smaller_than(int &err_ind,CUBE &A,int max);
void form_lngst_clause(CLAUSE &C0,CUBE &St);
void get_runtime (double &usrtime, double &systime);
void my_printf(const char *format,...);
void state_to_clauses(CNF &K,CUBE &A);
void read_numbers(char *buf,int &num1,int &num2);
void my_assert(bool cond);
void find_latch(Circuit *N,Gate &G,int &latch_ind);
void conv_to_vect(CCUBE &Name1,const char *Name0);
void conv_to_vect(CCUBE &Name1,std::string &Name0);
bool overlap(CUBE &A,CLAUSE &B);
int parse_string(CCUBE &Buff);
void print_names_of_latches(NamesOfLatches &Latches);
bool ident_arrays(CUBE &A,CUBE &B);
void print_blif2(FILE *fp,Circuit *N);
void print_blif3(const char *Name,Circuit *N);

extern long long gcount;
extern hsh_tbl htable_lits;

const int RESTORE = 0;
const int REPLACED=1;
const int ADD1=2;
const int ADD2=3;

// values of 'lit_pick_heur
const int RAND_LIT = 0;
const int INACT_LIT = 1;
const int INACT_VAR = 2;
const int FIXED_ORDER = 3;

// values of 'act_upd_mode'
const int NO_ACT_UPD = 0;
const int TF_ACT_UPD = 1;
const int MINISAT_ACT_UPD = 2;

// values of sorted_objects
const int LITS = 0;
const int VARS = 1;

// values of 'lift_sort_mode' and 'ind_cls_sort_mode'
const int NO_SORT = 0;
const int FULL_SORT = 1;
const int PART_SORT = 2;

// values of 'gate_sort_mode'
const int INIT_SORT = 0;
const int INPS_FIRST = 1;
const int OUTS_FIRST = 2;
const int RAND_SORT = 3;

// values of 'st_descr'
const char OLD_STATE = 0;
const char NEW_STATE = 1;
const char ROOT_STATE = 2;
const char PUSH_STATE = 3;
const char CTG_STATE = 4;
const char UNKNOWN_STATE = 5;

// values of 'grl_heur'
const int NO_JOINS = 0;
const int WITH_JOINS = 1;



const int  MAX_MARKER = 1000000; // used in hash tables

