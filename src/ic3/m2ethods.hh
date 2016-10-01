bool check_one_state_cex();
bool check_two_state_cex();
void ci_init();
int next_time_frame();
void form_one_state_cex(SatSolver &Slvr);
void form_two_state_cex(SatSolver &Slvr);
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
void add_fclause1(CLAUSE &C,int last_ind,char st_descr);
void form_conv_tables(char *root);
void conv_to_pres_state(CUBE &A,CUBE &B);
void conv_to_next_state(CUBE &A,CUBE &B);
bool gen_ind_clause(CLAUSE &C,CUBE &St,int tf_ind,char st_descr);
bool find_ind_subclause_cti(CLAUSE &C,SatSolver &Slvr,CLAUSE &C0,char st_descr);
void incr_short(CLAUSE &C,CLAUSE &C0,int curr_tf,char st_descr,int rec_depth);
void shorten_clause(CLAUSE &C,int curr_tf,CLAUSE &C0,char st_descr,
                   int rec_depth);
void add_new_clauses(SatSolver &Slvr,CUBE &Clauses);
void adjust_clause1(CLAUSE &C,CUBE &St);
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
bool find_prev_state_cube(CLAUSE &C,int curr_tf,CUBE &Erl_st,CUBE &Prev_inps,
                         CUBE &St_cube);
void check_conds();
void check_non_impl(CNF &Fn,CNF &H,int tf_ind);
void check_trans_cond(CNF &Fc,CNF &Fn);
void form_bnd_form(CNF &H,int i);
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
bool update_fclause(int clause_ind,int tf_ind);
void lift_bad_state(CUBE &Bst_cube,CUBE &St,CUBE &Inps);
void lift_good_state(CUBE &Gst_cube,CUBE &Pst,CUBE &Inps,CLAUSE &Nst_cube);
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
void add_new_elem(CUBE &St_cube,CUBE &Inp_assgn,int tf_ind,int dist,
                 int succ_ind,char descr);
void check_conv_tbl(CUBE &Vars,CUBE &Tbl,bool pres_svars);
bool oblig_is_active(int tf_ind,CUBE &St_cube);
bool cont_init_states(CUBE &St_cube);
void form_res_cnf(CNF &G,int tf_ind,CUBE &St_cube);
bool subsumes(CLAUSE &C,hsh_tbl &Ht);
void print_time_frame_sat_stat(int &time_frame_calls);
void print_all_calls(int time_frame_calls);
int replace_or_add_clause(int clause_ind,CLAUSE &C,int tf_ind);
void add_fclause2(CLAUSE &C,int last_ind,bool upd_activity);
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
void act_lit_init(CLAUSE &B,CUBE &Avail_lits,SCUBE &Tried_lits,
                  FltCube &Act0,FltCube &Act1);
void act_var_init(CLAUSE &B,CUBE &Avail_lits,SCUBE &Tried_lits,
                  FltCube &Act0,FltCube &Act1);
void sort_in_activity(CLAUSE &C1,CLAUSE &C,int sort_mode,bool reverse);
//
//
void add_tf0_clauses(SatSolver &Slvr);
void add_tf1_clauses(SatSolver &Slvr);
void add_tf2_clauses(SatSolver &Slvr);
bool ext_clause(CLAUSE &C);
void conv_to_mclause(TrivMclause &A, CLAUSE &C);
void load_clauses1(CNF &Ext_clauses,Minisat::SimpSolver *Sslvr,CNF &A);
void accept_simplified_form(SatSolver &Slvr,Minisat::SimpSolver *Sslvr);
void copy_simplified_form(Minisat::SimpSolver *Sslvr,CNF &Ext_clauses,
                          CNF &Uclauses);
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
void print_tf_assgns(int tf_ind);
void gen_unit_clauses(Minisat::SimpSolver *Sslvr,CNF &Uclauses);
void print_slv_stat(SatSolver &Slvr);
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
void add_new_latch(NamesOfLatches &Latches,Circuit *N,aiger_symbol &S);
void form_next_symb(CCUBE &Name,int lit);
void form_inv_names(CDNF &Pin_names,int lit);
void start_new_gate(CUBE &Gate_inds,Circuit *N,CDNF &Pin_names);
void form_gate_pin_names(CDNF &Pin_names,CUBE &Pol,aiger_and &Aig_gate);
void add_gate_inp_name(CCUBE &Name,int lit,CUBE &Pol);
void add_gate_out_name(CCUBE &Name,int lit,CUBE &Pol);
void form_gate_fun(Circuit *N,int gate_ind,CUBE &Pol);
//
bool find_ind_subclause_ctg(CLAUSE &C,int curr_tf,CLAUSE &C0,char st_descr,
                            int rec_depth,SCUBE &Failed_lits);
bool exclude_ctg(CUBE &St,int curr_tf,int rec_depth);
bool triv_ind_cls(int tf_ind,CUBE &St);
int latest_succ_tf_ind(int tf_ind,CLAUSE &C);
bool triv_ind_cls_proc(CLAUSE &Res,CLAUSE &C,int tf_ind);
bool adjust_clause2(CLAUSE &C,CUBE &St,SCUBE &Failed_lits);
int pick_lit_to_remove(CLAUSE &Curr,SCUBE &Tried,int curr_tf);
void lift_ctg_state(CUBE &Ctg_cube,CUBE &Ctg_st,CUBE &Inps,CUBE &Nxt_st);
void form_coi_array();
void form_coi(CUBE &Coi,CUBE &Stack,hsh_tbl &Htbl);
void conv_gates_to_svars(DNF &Coi_arr);
void form_stack(CUBE &Stack,CUBE &Latches);
void use_coi_to_drop_svars(CUBE &Nxt_cube,CUBE &Nxt_st,int curr_tf);
void extr_cut_assgns1(CUBE &Assgns,CUBE &Vars,SatSolver &Slvr);
void extr_cut_assgns2(CUBE &Assgns,CUBE &Lits,SatSolver &Slv);
void fxd_ord_init(CLAUSE &B,CUBE &Avail_lits,SCUBE &Tried);
int fxd_ord_lit(CUBE &Curr,SCUBE &Tried);
void store_constraints(aiger &A);
int upd_gate_constr_tbl(int lit,int gate_ind);
void upd_gate_constrs(aiger_and &Aig_gate,CUBE &Gate_inds);
bool check_constr_lits(int &fnd_lit,int lit);
void form_constr_lits();
void add_constrs();
void rem_constr_lits(CUBE &Lits1,CUBE &Lits0,SCUBE &Constr_lits);
void add_constr_lits(CUBE &St_cube);
bool init_st_satisfy_constrs();
void form_spec_simp_pr_tr(SatSolver &Slvr);
void load_clauses2(CNF &Ext_clauses,Minisat::SimpSolver *Sslvr,CNF &A,
                   int num_clauses);
void print_bnd_sets1();
void print_clause_state(int clause_ind);
//
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
