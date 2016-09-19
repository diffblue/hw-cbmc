/******************************************************

Module: Prototypes of functions used by the BLIF
        format reader

Author: Eugene Goldberg, eu.goldberg@gmail.com

******************************************************/
enum err_type {WRONG_EOF,WRONG_SYNTAX,CONSTANT_GATE};
#define eof_error 10
#define syn_error 20
#define constant_gate 30


//
//   Function propotypes
//
int blank_line(CCUBE &buf);
void skip_blanks(CCUBE &buf,int &i);
void copy_name(CCUBE &buf,CCUBE &name,int &i);
int compare(CCUBE &a,std::string const &b,int &i);
int str_size(std::string const &s);
int set_model(CCUBE buf,Circuit *N);
int create_inputs(CCUBE &buf,Circuit *N);
void add_input(CCUBE &name,Circuit *N,int inp_gate_num);
int create_outputs(CCUBE &buf,CDNF &Out_names);
void error_message(err_type error_name,CCUBE &buf);
void add_new_cube(CCUBE &buf,Circuit *N,int &gate_ind);
void finish_gate(Circuit *N,int &gate_ind);
void start_gate(CCUBE &buf,Circuit *N,int &gate_ind);
int add_latch(CCUBE &buf,NamesOfLatches &Latches,Circuit *N,int &gate_ind);
void fill_fanout_lists(Circuit *N);
void check_fanout_free_inputs(Circuit *N,reader_state &r);
void assign_gate_type(Circuit *N,CDNF &Out_names,bool rem_dupl_opt);
void  assign_levels_from_inputs(Circuit *N);
void  assign_levels_from_outputs(Circuit *N);
void print_gate_names(CDNF &A);
void  print_names(FILE *fp,Circuit *N,CUBE &gates);
void fprint_name(FILE *fp,CCUBE &name);
void print_name(CCUBE *name);
void print_cube(FILE *fp,CUBE &C,int ninputs);
void print_all_info(FILE *fp,Circuit *N);
void print_gate_name(Gate &G);
Circuit *create_circuit(void);
void delete_circuit(Circuit *N);
void init_gate_fields(Gate &G);
Circuit  *read_blif(FILE *fp,NamesOfLatches &Latches,reader_state &r);
int assign_output_pin_number(std::map<CCUBE,int> &pin_list,CCUBE &name,GCUBE &gate_list,bool latch);
int assign_input_pin_number1(std::map<CCUBE,int> &pin_list,CCUBE &name,GCUBE &gate_list);
int assign_input_pin_number2(NamesOfLatches &Latches,Circuit *N,CCUBE &name,GCUBE &gate_list);
void set_trans_output_fun_flags(Circuit *N);
void set_feeds_latch_flag(Circuit *N,bool ignore_errors,bool rem_dupl_opt);
void  print_gate_type(FILE *fp,Circuit *N,Gate &G);
void fill_up_levels(Circuit *N, DNF &Level_gates);
void print_latch_levels(Circuit *N);
void circ_print_header(FILE *fp,Circuit *N);
void print_latch(FILE *fp,Circuit *N,Gate &G);
int read_string(FILE *fp,CCUBE &buf);
Command_type  identify_command(CCUBE &buf);
void gen_fake_name(CCUBE &fake_name,int ind);
void add_spec_buffs(Circuit *N);
void add_one_spec_buff(Circuit *N,int ind);
int spec_buff_gate_ind(Circuit *N,int ind);
void start_spec_buff(Circuit *N,int gate_ind);
void add_spec_buff_cube(Circuit *N,int gate_ind);
void finish_spec_buff(Circuit *N,int gate_ind);
void gen_spec_buff_name(Circuit *N);
bool name_clash(CCUBE &Root_name,Circuit *N,int gate_ind);
void form_output_name(CCUBE &Name,Circuit *N,int gate_ind);
void form_fanin_list(Circuit *N,int gate_ind);
void set_input_polarity(CUBE &C,Gate &G);

