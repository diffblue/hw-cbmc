/******************************************************

Module: Prototyps of member functions used by IC3

Author: Eugene Goldberg, eu.goldberg@gmail.com

******************************************************/
bool check_one_state_cex();
bool check_two_state_cex();
void ci_init();
int next_time_frame();
void form_one_state_cex(SatSolver &Slvr);
void form_two_state_cex(SatSolver &Slvr);
void extr_pres_state(CUBE &St,SatSolver &Slvr);
void extr_next_state(CUBE &St,SatSolver &Slvr);
void form_property();
void form_short_property();
void form_bad_states();
void form_bad_states0(CNF &Bstates);
void exclude_state_cube(CNF &G,int &min_tf,CUBE &St,CUBE &Inps);
void push_clauses_forward();
void init_time_frame_solver(int tf_ind);
void init_bst_sat_solver();
void init_lbs_sat_solver();
void init_lgs_sat_solver();
void add_fclause1(CLAUSE C,int last_ind);
void form_conv_tables(char *root);
void conv_to_pres_state(CUBE &A,CUBE &B);
void conv_to_next_state(CUBE &A,CUBE &B);
bool gen_ind_clause(CLAUSE &C,CUBE &St,int tf_ind,char st_descr);
bool lngst_ind_clause(CLAUSE &C,SatSolver &Slvr,CLAUSE &C0,char st_descr);
void incr_short(CLAUSE &C,int curr_tf,CLAUSE &C0,char st_descr);
void shorten_clause(CLAUSE &C,int curr_tf,CLAUSE &C0,char st_descr);
void add_new_clauses(SatSolver &Slvr,CUBE &Clauses);
void adjust_clause(CLAUSE &C,CUBE &St);
bool corr_clause(CLAUSE &C);
bool push_clause(CLAUSE &C,int tf_ind,int clause_ind);
bool ver_ini_states(CNF &H);
bool ver_prop();
bool ver_ind_clauses1(CNF &H);
bool ver_ind_clauses2(CNF &H,CUBE &Old_nums);
bool ver_invar(CNF &H,CUBE &Old_nums);
void gen_form1(CNF &H,int k);
void gen_form2(CNF &H,CUBE &Old_nums,int k);
bool check_init_state(CUBE &St);
bool check_transition(CUBE &St0,CUBE &St1);
bool check_bad_state(CUBE &St);
bool find_prev_state_cube(CLAUSE &C,int curr_tf,CUBE &Erl_st,CUBE &Prev_inps,CUBE &St_cube);
void find_wrong_transition(CUBE &St0,CUBE &St1,SatSolver &Slvr);
void add_neg_prop(SatSolver &Slvr);
void modif_loc_clause(CLAUSE &C,CUBE &St);
bool time_to_terminate();
float average();
int find_rand_lit(CLAUSE &Curr,SCUBE &Tried);
void rem_lit(CLAUSE &Curr,int lit);
void modif_ind_clause(CLAUSE &C1,CLAUSE &C);
void print_sat_stat();
void print_one_sat_stat(SatSolver &Slvr);
void add_bad_states(SatSolver &Slvr);
void compos_short(CLAUSE &C,CLAUSE &C0,int curr_tf,char st_descr);
void find_avail_lits(CUBE &Avail_lits,CLAUSE &C);
void rand_init(CLAUSE &B,CUBE &Avail_lits,SCUBE &Tried_lits);
void find_fixed_pnt(CLAUSE &C,CLAUSE &C0,SatSolver &Slvr,char st_descr);
int add_missing_lits(CLAUSE &C,CLAUSE &B);
void update_fclause(int clause_ind,int tf_ind);
void lift_bad_state(CUBE &Bst_cube,CUBE &St,CUBE &Inps);
void lift_good_state(CUBE &Gst_cube,CUBE &Pst,CUBE &Inps,CLAUSE &Nst_cube);
void extr_pres_inps(CUBE &Inps,SatSolver &Slvr);
void extr_next_inps(CUBE &Inps,SatSolver &Slvr);
void check_overlapping();
void gen_state_cube(CUBE &St_cube,CUBE &St,SatSolver &Slvr);
void form_init_st(CUBE &St_cube);
void form_missing_nxt_svars();
void add_time_frame();
void empty_cnts();
void print_time_frame_stat();
void add_copies(int tf_ind,CLAUSE &C);
void add_one_copy(int tf_ind,CLAUSE &C);
void form_inp_trace(DNF &Inp_trace);
void add_new_elem(CUBE &St_cube,CUBE &Inp_assgn,int tf_ind,int dist,int succ_ind,char descr);
void check_conv_tbl(CUBE &Vars,CUBE &Tbl,bool pres_svars);
bool oblig_is_active(int tf_ind,CUBE &St_cube);
bool cont_init_states(CUBE &St_cube);
void form_res_cnf(CNF &G,int tf_ind,CUBE &St_cube);
bool tr_rel_clause(CLAUSE &C);
bool clause_overlap(CLAUSE &C,hsh_tbl &Ht);
bool subsumes(CLAUSE &C,hsh_tbl &Ht);
void print_time_frame_sat_stat(int &time_frame_calls);
void print_all_calls(int time_frame_calls);
int replace_or_add_clause(int clause_ind,CLAUSE &C,int tf_ind);
void add_fclause2(CLAUSE C,int last_ind,bool upd_activity);
void init_fields();
//
//
void form_max_pres_svar();
void remove_clause(int clause_ind);
int rem_redund_clauses();
void sort_in_length(CUBE &Old_nums);
void form_lit_arrays(CUBE &Old_nums);
int find_best_ind2(CLAUSE &C);
void check_for_subsumed_clauses1(CUBE &Subsumed,int clause_ind);
void mark_literals(hsh_tbl &Ht,CLAUSE &C);
void clean_clause_set();
void clean_formula();
void build_new_clause_table();
void recomp_tf_cls_sets();
void print_flags();
int find_inact_lit(CLAUSE &Curr,SCUBE &Tried,FltCube &Act0,FltCube &Act1);
int find_inact_var(CLAUSE &Curr,SCUBE &Tried,FltCube &Act0,FltCube &Act1);
void upd_act_lit_cnts(CLAUSE &C,int last_ind);
void scale_factor_down(float min_act);
void act_lit_init(CLAUSE &B,CUBE &Avail_lits,SCUBE &Tried_lits,FltCube &Act0,FltCube &Act1);
void act_var_init(CLAUSE &B,CUBE &Avail_lits,SCUBE &Tried_lits,FltCube &Act0,FltCube &Act1);
void comput_rec_lit_act(int curr_tf);
void sort_in_activity(CLAUSE &C1,CLAUSE &C,int sort_mode,bool reverse);
//
//
void add_tf0_clauses(SatSolver &Slvr);
void add_tf1_clauses(SatSolver &Slvr);
void add_tf2_clauses(SatSolver &Slvr);
bool ext_clause(CLAUSE &C);
void conv_to_mclause(TrivMclause &A, CLAUSE &C);
void load_clauses(CNF &Ext_clauses,Minisat::SimpSolver *Sslvr,CNF &A);
void accept_simplified_form(SatSolver &Slvr,Minisat::SimpSolver *Sslvr);
void copy_simplified_form(Minisat::SimpSolver *Sslvr,CNF &Ext_clauses,CNF &Uclauses);
void add_assumps1(MvecLits &Assmps,CUBE &St);
void add_assumps2(MvecLits &Assmps,CUBE &St);
void add_assumps3(MvecLits &Assmps,CUBE &St);
void release_lit(SatSolver &Slvr,Mlit lit);
bool check_sat1(SatSolver &Slvr);
bool check_sat2(SatSolver &Slvr,MvecLits &Assmps);
void add_negated_assumps1(MvecLits &Assmps,CLAUSE &C);
void add_negated_assumps2(MvecLits &Assmps,CLAUSE &C,bool sort);
void gen_assump_clause(CLAUSE &C,SatSolver &Slvr,MvecLits &Assmps);
void add_cls_excl_st_cube(Mlit &act_lit,SatSolver &Slvr,CUBE &St);
void add_temp_clause(Mlit &act_lit,SatSolver &Slvr,CLAUSE &C);
void simplify_tf_solvers();
void gen_unit_clauses(Minisat::SimpSolver *Sslvr,CNF &Uclauses);
void build_arrays();
void print_sort_mode(const char *mode_name,int sort_mode) ;
void full_sort(CLAUSE &C1,CLAUSE &C, std::vector <ActInd> &V);
void part_sort(CLAUSE &C1,CLAUSE &C, std::vector <ActInd> &V);
void print_lifting_stat();
//
void form_inputs(Circuit *N,aiger &Aig);
void form_output(int &outp_lit,Circuit *N,aiger &Aig);
void form_latches(Circuit *N,aiger &Aig);
void form_gates(Circuit *N,aiger &Aig);
void form_outp_buf(CDNF &Out_names,Circuit *N,int outp_lit);
void form_invs(Circuit *N);
void form_consts(Circuit *N);
void add_new_latch(Circuit *N,aiger_symbol &S);
void form_next_symb(CCUBE &Name,int lit);
void form_inv_names(CDNF &Pin_names,int lit);
int start_new_gate(Circuit *N,CDNF &Pin_names);
void form_gate_pin_names(CDNF &Pin_names,CUBE &Pol,aiger_and &Aig_gate);
void add_gate_inp_name(CCUBE &Name,int lit,CUBE &Pol);
void add_gate_out_name(CCUBE &Name,int lit,CUBE &Pol);
void form_gate_fun(Circuit *N,int gate_ind,CUBE &Pol);
void print_clause_state(int clause_ind);
void print_bnd_sets1();

// member functions
void gen_trans_rel(int shift);
void gen_cnfs(char *fname,bool print_flag);
void gen_out_fun(DNF &H,int shift,bool short_version);
void form_pres_state_vars();
void form_next_state_vars();
void form_inp_vars();
void form_pres_to_next_conv();
void form_next_to_pres_conv();
void assign_var_indexes();
void add_last_cube(DNF &F);
void form_property_gates(CUBE &Gates);
void print_files(char *root);

//
//  print out gates
void add_or_gate_cubes(DNF &F,int gate_ind,int shift);
void add_truth_table_gate_cubes(DNF &F,int gate_ind,int shift);
void add_const_gate_cube(DNF &F,int gate_ind,int shift);
void add_and_gate_cubes(DNF &F,int gate_ind,int shift);
void  add_buffer_gate_cubes(DNF &F,int gate_ind,int shift);
void  gen_initial_state_cubes();

// debugging methods
void print_var_indexes();
void print_var_indexes(char *name);
