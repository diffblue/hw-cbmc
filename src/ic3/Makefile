CXXFLAGS = -std=c++0x  -Wno-literal-suffix -Wno-write-strings -D __STDC_LIMIT_MACROS -D __STDC_FORMAT_MACROS  -Wno-parentheses -Wno-sign-compare -O3
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
vpath %.h aiger
vpath %.c aiger

MROOT = minisat
MLIB  = minisat/build/dynamic/lib/libminisat.so
SLIB = 	minisat/build/release/lib/libminisat.a


INC_DIR = -I. -Ibuild_prob -Iseq_circ -I$(MROOT) -I$(MROOT)/minisat/core -I$(MROOT)/minisat/mtl -I$(MROOT)/minisat/simp -Iaiger


BUILD_PROB =   obj/g0en_cnf.o obj/g1en_cnf.o obj/g2en_cnf.o \
               obj/assign_indexes.o obj/build_arrays.o

SEQ_CIRC = obj/r1ead_blif.o obj/r2ead_blif.o obj/r3ead_blif.o \
           obj/c2irc_util.o obj/c3irc_util.o \
           obj/l0ast_touch.o obj/l1ast_touch.o  \
           obj/a2dd_gate.o obj/a3dd_gate.o  obj/preamble.o  \
           obj/circuit.o   obj/finish_gate.o  


OBJ_ROOT = obj/m1ain.o  obj/p1arameters.o  obj/o1utput.o \
           obj/r0ead_input.o  obj/r1ead_input.o obj/r2ead_input.o obj/r3ead_input.o \
           obj/i1nit.o obj/i2nit_sat_solvers.o obj/i3nit_sat_solvers.o  obj/interface.o \
           obj/next_time_frame.o obj/e1xclude_state.o obj/e2xclude_state.o \
           obj/e3xclude_state.o  obj/e4xclude_state.o obj/e5xclude_state.o\
           obj/p0ick_lit.o  \
           obj/u0til.o obj/u1til.o  obj/u2til.o  obj/u3til.o \
           obj/s1tat.o obj/s3tat.o  obj/my_printf.o \
           obj/p2ush_clauses_forward.o  obj/p3ush_clauses_forward.o  \
           obj/find_red_cls.o obj/lift_states.o  obj/s2horten_clause.o  \
           obj/c0ex.o obj/v0erify.o obj/v1erify.o \
           obj/c1onv_vars.o obj/hash_table.o  obj/dnf_io.o \


AIGER = obj/aiger.o 

OBJ =     $(OBJ_ROOT) $(SEQ_CIRC)  $(BUILD_PROB)  $(AIGER)


obj/%.o : %.cc m0ic3.hh dnf_io.hh  m2ethods.hh aux_types.hh i4nline.hh r0ead_blif.hh ccircuit.hh
	$(CXX) -c $(CXXFLAGS) $(INC_DIR) $< -o $@
obj/%.o : %.c
	$(CC) -c $(ARCH_FLAG) $(CFLAGS) $< -o $@


LINK_OPTIONS =



$(PROG_NAME) :  $(DLIB) $(OBJ)
	$(CXX)  $(LINK_OPTIONS) $(ARCH_FLAG)  $(OBJ) $(SLIB) -o  $(PROG_NAME)

all :  $(OBJ)
	$(CXX)  $(LINK_OPTIONS) $(ARCH_FLAG)  $(OBJ) 	$(SLIB) -o  $(PROG_NAME)

clean : 
	rm -f obj/*.o  ic3 aic3 *~
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

