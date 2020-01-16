void add_input(CCUBE &name,Circuit *N,int inp_gate_num);
void finish_gate(Circuit *N,int &gate_ind,messaget &M);
void fill_fanout_lists(Circuit *N,messaget &M);
void assign_gate_type(Circuit *N,CDNF &Out_names,bool rem_dupl_opt,messaget &M);
void  assign_levels_from_inputs(Circuit *N,messaget &M);
void  assign_levels_from_outputs(Circuit *N,messaget &M);
void  print_names(std::ofstream &Out_str,Circuit *N,CUBE &gates);
void print_name(CCUBE *name);
Circuit *create_circuit(void);
void init_gate_fields(Gate &G);
int assign_output_pin_number(std::map<CCUBE,int> &pin_list,CCUBE &name,
			     GCUBE &gate_list,bool latch,messaget &M);
int assign_input_pin_number1(std::map<CCUBE,int> &pin_list,CCUBE &name,
			     GCUBE &gate_list);
int assign_input_pin_number2(NamesOfLatches &Latches,Circuit *N,CCUBE &name,
			     GCUBE &gate_list);
void set_trans_output_fun_flags(Circuit *N);
void set_feeds_latch_flag(Circuit *N,bool ignore_errors,bool rem_dupl_opt,
			  messaget &M);
void fill_up_levels(Circuit *N, DNF &Level_gates);
void circ_print_header(std::ofstream &Out_str,Circuit *N);
void print_latch(std::ofstream &Out_str,Circuit *N,Gate &G);
void gen_fake_name(CCUBE &fake_name,int ind);
void add_spec_buffs(Circuit *N,messaget &M);
void add_one_spec_buff(Circuit *N,int ind,messaget &M);
int spec_buff_gate_ind(Circuit *N,int ind);
void start_spec_buff(Circuit *N,int gate_ind);
void add_spec_buff_cube(Circuit *N,int gate_ind);
void finish_spec_buff(Circuit *N,int gate_ind,messaget &M);
void gen_spec_buff_name(Circuit *N);
void set_input_polarity(CUBE &C,Gate &G);

