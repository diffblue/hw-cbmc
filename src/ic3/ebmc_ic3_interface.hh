typedef std::vector<std::string> GateNames;
typedef std::map<int,int> LatchVal;
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
  unsigned max_var;
  bool const0,const1;

  int operator()();
  void read_ebmc_input();  
  void find_prop_lit();
  void ebmc_form_latches();
  void gen_ist_lits(bvt &Ist_lits);
  void form_circ_from_ebmc();
  void form_inputs();
  void form_latched_gates();
  void add_new_latch(NamesOfLatches &Latches,
  		   int init_val,int pres_lit_val,literalt &next_lit);
  void form_next_symb(CCUBE &Name,literalt &next_lit);
  void form_gates();
  void form_gate_pin_names(CDNF &Pin_names,CUBE &Pol,int node_ind);
  void add_gate_inp_name(CCUBE &Name,literalt &lit,CUBE &Pol);
  void add_gate_out_name(CCUBE &Name,literalt &lit,CUBE &Pol);
  void upd_gate_constrs(int node_ind,CUBE &Gate_inds);
  void form_outp_buf(CDNF &Out_names);
  void comp_num_nodes();

protected:
  netlistt netlist;
 

};








