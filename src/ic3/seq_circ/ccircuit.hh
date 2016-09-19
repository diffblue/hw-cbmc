/******************************************************

Module: Basic types (gate, circuit and so on) 
        and function prototypes

Author: Eugene Goldberg, eu.goldberg@gmail.com

******************************************************/
// TRUTH_TABLE means neither "CONST",'BUFFER','AND','OR' gate and the cubes describing the ON-set have no don't cares
enum Func_type {CONST,BUFFER,AND,OR,TRUTH_TABLE,COMPLEX};
enum Gate_type {INPUT,GATE,LATCH,UNDEFINED};
enum Command_type {DOT_NAMES,DOT_LATCH,DOT_END,WRONG};
// INPUT - primary input,   
// GATE means a combinational gate
// LATCH means latch
// UNDEFINED is used to initialize the type of combinational gates

struct GateFlagsType {
  unsigned active : 1; // a deletion flag
  unsigned label : 1; // used to mark gates during search 
  unsigned output : 1; // is set to one if the output of the gate is also the output of the circuit
  unsigned transition : 1; // is set to 1 if there is a path from the output of this gate to a latch 
                           // (and so this gate is a part of transition relation)
  unsigned output_function : 1; // is set to 1 if there is a path from the output of this gate to a primary output
                                // (and so this gate is a part of the circuit specifying the output function
  unsigned feeds_latch: 1; // is set to 1 if the output of the gate feeds a latch
  unsigned redund :1; // is set to 1 when the gate describes a latch that is redudnant
};

/*=============================

  C L A S S   G A T E

  ==============================*/
class Gate {
public:
  int ninputs; // number of inputs
  Func_type func_type; // whether it is  a BUFFER, AND  or OR gate or COMPLEX
  Gate_type gate_type; // the possible types are:  input, gate, latch, undefined
  CCUBE Polarity; // set polarity of inputs and output
  CUBE Fanin_list; // indexes of gates connected to inputs of this gate
  CUBE Fanout_list; // indexes of gates connected to the output of this gate
  char init_value; // used for latches
  GateFlagsType flags; // used to set property flags
  //  char active; // deletion flag 
  int level_from_inputs; // topological level of the gate giving the length of the longest path from an input to this gate.
                         //  It is equal to 0 for the input gates and latches.
  int level_from_outputs; //  topological level of the gate giving the length of the longest path from an output 
                          // It is equal to 0 for output nodes that do not feed other outputs and for the latches 
  CCUBE Gate_name; // gate name
  // char label; // just a variable to mark this node during search
  // F and R DNFs are non-empty only if the Func_type of the gate is COMPLEX
  DNF F; // the ON-set 
  DNF R; // the OFF-set
  int eq_class_rep; // specifies the latch that was non-redundant at the time the current latch was proved
  // redundant

  // the two data members below are used for special buffers used to address the problem of gates
  // feeding more than one latch
  int seed_gate; // if 'seed_gate >= 0', it points to a gate feeding more than one latch
  int spec_buff_ind;  // if 'spec_buff_ind >= 0' it specifies the index of the special buffer index
  bool inp_feeds_latch; // is used when an input feeds more than one latch
};

typedef std::vector <Gate> GCUBE;
/*====================================

  C L A S S   C I R C U I T

  =====================================*/
class Circuit
{
public:
  int ninputs; // number of primary inputs
  int noutputs; // number of primary outputs
  int nlatches; // number of latches
  int ngates; // contains the number of gates (not counting input nodes)
  int nconstants; // number of constants
  int max_levels; // contains the maximal topological level of a gate
  GCUBE Gate_list; // list of gates (includes input nodes and latches)
  CCUBE Circuit_name; /* circuit name */
  CUBE Inputs; // numeric  labels of input nodes
  CUBE Outputs; // numeric labels of output nodes
  CUBE Latches; // numeric labels of latch nodes
  CUBE Constants; // numeric labels of nodes that are constants
  std::map<CCUBE,int> Pin_list; // allows to find 'gate_ind' by name
  
 
  // the two data members below are used to address the problem of gates
  //  feeding more than one latch
 
  int num_spec_buffs; // current number of special buffers 
  CCUBE Spec_buff_name; // specifies the root name of special buffers

  //
  //  methods 
  //

  inline  Gate &get_gate(int gate_num){return(this->Gate_list[gate_num]);};
  inline bool ext_gate(Gate &G) {return((G.flags.output == 1) && (G.Fanout_list.size() == 0));};
  inline bool ext_int_gate(Gate &G) {return((G.flags.output == 1) && (G.Fanout_list.size() > 0));};
  inline bool output_gate(Gate &G) {return(G.flags.output == 1);};
  bool mark_duplicates(Gate &G);
  bool print_without_duplicates();
  void print_fanout_stat();
  int find_max_fanout_num();
  void comp_fanout_distrib(CUBE &A);
  void print_fanout_distrib(CUBE &A);
  void find_remaining_red_latches();
  void clean_latches();
  void print_names1(FILE *fp,CUBE &gates,bool latch_flag);
  void print_latch1(FILE *fp,Gate &G);
  void print_gate1(FILE *fp,Gate &G);
  void find_eq_class_reps();
  void finish_marking_red_latches();
  int find_rep(Gate &G);
  void print_no_fanout_gates();
};

#define MAX_LINE 10000

class reader_state
{
public:
  bool ignore_missing_end; // go on if the .blif file does have the '.end' command
  bool add_buffers; // if there is an input and output with the same name add a buffer gate
  bool check_fanout_free_inputs; // is set to false by default
  bool unfinished_gate; // is set to true when '.names' command occurs. 
  bool rem_dupl_opt; // is set to 'true' if elimination of multiple-fanout of a gate feeding latches is required
  bool ignore_errors; // if true, results of (some) correctness assertions are ignored
  reader_state(void);
};

#define n() {printf("\n");}
//
// constants
//
const int  NAMES_MAX = 10;
const int MAX_NAME = 100;

//
//  functions   
//
void clear_labels(Circuit *N);
void print_gate(FILE *fp,Circuit *N,Gate &G);
void print_gate_name(Gate &G);
void print_gate_name1(Gate &G);
void fprint_name(FILE *fp,CCUBE &name);
void  print_levels(Circuit *N);
void print_name1(CCUBE &name);
void print_subcircuit(Circuit *N,CCUBE &name);
void rename_gates(Circuit *N,char C);
void print_tr_rel(Circuit *N,char *root);
void print_tr_rel_header(Circuit *N,FILE *Tr_rel,char *root);
void print_st_vars(Circuit *N,char *root);
void print_inp_vars(Circuit *N,char *root);
void print_const(FILE *fp,Circuit *N,Gate &G);
void self_looping_latches(Circuit *N);
bool feeds_only_property(Circuit *N,Gate &G);
bool feeds_only_latches_or_property(Circuit *N,Gate &G);
void print_latch_stat(Circuit *N);
void form_spec_latches(Circuit *N,CUBE &Spec_latches);
void add_spec_latches(FILE *Tr_rel,Circuit *N,CUBE &Spec_latches);
int get_fanout_latch(Circuit *N,CUBE &Fanout_gates);
void print_gates_for_spec_latches(FILE *Tr_rel,Circuit *N,CUBE &Spec_latches);
void print_latch_fed_by_input(FILE *Tr_rel,Gate &G1,Gate &G,int loc_ind);
void print_latch_fed_by_const(FILE *Tr_rel,Gate &G1,Gate &G,int loc_ind);
void my_printf(char *format,...);
void remove_unobserv_gates(Circuit *N);
void print_header1(Circuit *N);
void print_names2(Circuit *N,CUBE &gates);

