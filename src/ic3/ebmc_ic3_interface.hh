typedef std::vector<std::string> GateNames;
typedef std::map<int,int> LatchVal;
typedef std::map<int,int> NondetVars;
//
class ic3_enginet:public ebmc_baset
{
public:
  ic3_enginet(
	      const cmdlinet &cmdline,
	      ui_message_handlert &ui_message_handler):
    ebmc_baset(cmdline, ui_message_handler)
  {
  }

  CompInfo Ci;
  GateNames Gn;
  literalt prop_l;
  LatchVal Latch_val;
  NondetVars Nondet_vars;
  bool const0,const1;
  bool orig_names;

  int operator()();
  void read_ebmc_input();  
  void find_prop_lit();
  void ebmc_form_latches();
  void gen_ist_lits(bvt &Ist_lits);
  void form_circ_from_ebmc();
  void form_inputs();
  void form_latched_gates();
  void add_new_latch(NamesOfLatches &Latches,
  		   int init_val,literalt &pres_lit,literalt &next_lit);
  void form_next_symb(CCUBE &Name,literalt &next_lit);
  void form_gates();
  void form_gate_pin_names(CDNF &Pin_names,CUBE &Pol,int node_ind);
  void add_gate_inp_name(CCUBE &Name,literalt &lit,CUBE &Pol);
  void add_gate_out_name(CCUBE &Name,literalt &lit,CUBE &Pol);
  void upd_gate_constrs(int node_ind,CUBE &Gate_inds);
  void form_outp_buf(CDNF &Out_names);
  void form_latch_name(CCUBE &Latch_name,literalt &lit);
  //
 
  void print_lit1(unsigned var,bool sign);
  void print_lit2(unsigned var,bool sign);
  void print_nodes();
  void print_var_map(std::ostream &out);
  void form_orig_names();
  void form_neg_orig_name(CCUBE &Name,literalt &next_lit);
  bool form_orig_name(CCUBE &Name,literalt &lit,bool subtract = false);
  void form_inv_names(CDNF &Pin_names,int lit);
  void form_invs();
  void print_expr_id(exprt &E);
  bool banned_expr(exprt &expr);
  bool find_prop(propertyt &Prop);
  void read_parameters();
  void print_header();
  void form_init_constr_lits();
  void store_constraints(const std::string &fname);
  void read_constraints(const std::string &fname);
  void add_pseudo_inps(Circuit *N);
  void print_lit(std::ostream& out,literalt a);
  std::string print_string(const irep_idt &id);
  void add_verilog_conv_constrs();
  
protected:
  netlistt netlist;
 

};

//
std::string short_name(const irep_idt &Lname);
