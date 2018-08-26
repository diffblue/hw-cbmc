
CXXFLAGS = -Wno-write-strings -D __STDC_LIMIT_MACROS -D __STDC_FORMAT_MACROS -O3 $(INC_DIR)

CXFLAGS = $(INC_DIR)
CFLAGS =   -O3  $(INC_DIR) 
CXX = g++
CC = gcc
ARCH_FLAG =

PROG_NAME = ic3

vpath %.cc seq_circ
vpath %.hh seq_circ
vpath %.cc build_prob
vpath %.hh build_prob

include ../config.inc

MINISAT_INC = minisat

INC_DIR = -I . -I build_prob -I seq_circ -I $(MINISAT_INC) -I $(CBMC)/src -I ../

CXXFLAGS += -D'LOCAL_IREP_IDS=<hw_cbmc_irep_ids.h>'

OBJ_DIR = .

BUILD_PROB =   $(OBJ_DIR)/g3en_cnf.o  $(OBJ_DIR)/g0en_cnf.o $(OBJ_DIR)/g1en_cnf.o \
               $(OBJ_DIR)/g2en_cnf.o $(OBJ_DIR)/assign_indexes.o $(OBJ_DIR)/build_arrays.o

SEQ_CIRC = $(OBJ_DIR)/p1rint_blif.o $(OBJ_DIR)/p2rint_blif.o $(OBJ_DIR)/finish_gate.o \
           $(OBJ_DIR)/a2dd_gate.o  $(OBJ_DIR)/a3dd_gate.o  $(OBJ_DIR)/c2irc_util.o \
           $(OBJ_DIR)/circuit.o $(OBJ_DIR)/a4dd_spec_buffs.o  $(OBJ_DIR)/a5dd_spec_buffs.o  \
           $(OBJ_DIR)/l0ast_touch.o $(OBJ_DIR)/l1ast_touch.o 
     
OBJ_ROOT = $(OBJ_DIR)/m5y_aiger_print.o \
           $(OBJ_DIR)/m4y_aiger_print.o  $(OBJ_DIR)/r7ead_input.o $(OBJ_DIR)/r6ead_input.o  \
           $(OBJ_DIR)/g2ate_ord.o $(OBJ_DIR)/i4nit_sat_solvers.o $(OBJ_DIR)/l1ift_states.o \
           $(OBJ_DIR)/r5ead_input.o  $(OBJ_DIR)/r4ead_input.o $(OBJ_DIR)/c4oi.o \
           $(OBJ_DIR)/c5tg.o $(OBJ_DIR)/c2tg.o $(OBJ_DIR)/r3ead_input.o \
           $(OBJ_DIR)/r2ead_input.o $(OBJ_DIR)/r1ead_input.o $(OBJ_DIR)/r0ead_input.o \
           $(OBJ_DIR)/dnf_io.o  $(OBJ_DIR)/m1ain.o $(OBJ_DIR)/p1arameters.o \
           $(OBJ_DIR)/i3nit_sat_solvers.o $(OBJ_DIR)/interface.o $(OBJ_DIR)/u3til.o \
           $(OBJ_DIR)/s3tat.o $(OBJ_DIR)/p5ick_lit.o $(OBJ_DIR)/p0ick_lit.o \
           $(OBJ_DIR)/find_red_cls.o $(OBJ_DIR)/u2til.o  $(OBJ_DIR)/e5xclude_state.o \
           $(OBJ_DIR)/p3ush_clauses_forward.o $(OBJ_DIR)/i2nit_sat_solvers.o $(OBJ_DIR)/l0ift_states.o \
           $(OBJ_DIR)/u1til.o $(OBJ_DIR)/s2horten_clause.o $(OBJ_DIR)/u0til.o \
           $(OBJ_DIR)/e4xclude_state.o $(OBJ_DIR)/s1tat.o  $(OBJ_DIR)/e3xclude_state.o \
           $(OBJ_DIR)/v1erify.o $(OBJ_DIR)/o1utput.o $(OBJ_DIR)/v0erify.o \
           $(OBJ_DIR)/p2ush_clauses_forward.o $(OBJ_DIR)/e2xclude_state.o \
           $(OBJ_DIR)/e1xclude_state.o $(OBJ_DIR)/c1onv_vars.o \
           $(OBJ_DIR)/c0ex.o $(OBJ_DIR)/i1nit.o $(OBJ_DIR)/next_time_frame.o \
           $(OBJ_DIR)/hash_table.o  $(OBJ_DIR)/my_printf.o


OBJ =      $(OBJ_ROOT) $(BUILD_PROB) $(SEQ_CIRC)

H_FILES1 = m0ic3.hh dnf_io.hh  m2ethods.hh aux_types.hh i5nline.hh
H_FILES2 = ccircuit.hh ebmc_ic3_interface.hh more_fun_prot.hh
$(OBJ_DIR)/%.o : %.cc  $(H_FILES1) $(H_FILES2)
	$(CXX) -c $(CXXFLAGS)  $< -o $@
$(OBJ_DIR)/%.o : %.c
	$(CC) -c $(ARCH_FLAG) $(CFLAGS) $< -o $@

CLEANFILES = $(PROG_NAME)

LINK_OPTIONS =

LIB_PATH = 	minisat/build/release/lib


all : libic3.a make_minisat

libic3.a: $(OBJ)
	ar rc $@ $(OBJ)
	ranlib $@

make_minisat: 
	cd minisat; make lr

clean : clean_ic3 clean_minisat

clean_ic3:
	rm -f $(OBJ_DIR)/*.o $(OBJ_DIR)/*.d ic3 aic3 libic3.a *~

clean_minisat:
	cd minisat; make clean

debug   :
	make "CXXFLAGS=-g $(CXFLAGS)" all
prof : 
	make  "CXXFLAGS=$(CXFLAGS) -pg" "LINK_OPTIONS=$(LINK_OPTIONS) -pg" all
prof1: 
	make  "CXXFLAGS=$(CXXFLAGS) -pg -g" "LINK_OPTIONS=$(LINK_OPTIONS) -pg"
opt: 
	make  "CXXFLAGS=$(CXXFLAGS) -O3" 
static:
	make  "CXXFLAGS=$(CXXFLAGS) -O3 -static" "LINK_OPTIONS= -static"

