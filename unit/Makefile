.PHONY: test

# Main
SRC = unit_tests.cpp

# Test source files
SRC += ebmc/bdd_model_checker.cpp \
       ebmc/transition_property.cpp \
       fastppa/estimate.cpp \
       fastppa/technology_db.cpp \
       smvlang/expr2smv.cpp \
       temporal-logic/hoa.cpp \
       temporal-logic/ltl_sva_to_string.cpp \
       temporal-logic/rewrite_sva_sequence.cpp \
       temporal-logic/sva_sequence_match.cpp \
       temporal-logic/sva_to_ltl.cpp \
       temporal-logic/nnf.cpp \
       temporal-logic/trivial_sva.cpp \
       trans-netlist/aig.cpp \
       trans-netlist/id2smv.cpp \
       verilog/convert_literals.cpp \
       verilog/indexed_part_select.cpp \
       verilog/typename.cpp \
       verilog/verilog_expr.cpp \
       # Empty last line

INCLUDES= -I ../src/ -I . -I $(CPROVER_DIR)/unit -I $(CPROVER_DIR)/src

CPROVER_DIR = ../lib/cbmc

include $(CPROVER_DIR)/src/config.inc
include $(CPROVER_DIR)/src/common

CXXFLAGS += -D'LOCAL_IREP_IDS=<hw_cbmc_irep_ids.h>'

OBJ += ../src/ebmc/bdd_model_checker$(OBJEXT) \
       ../src/ebmc/transition_property$(OBJEXT) \
       ../src/ebmc/transition_system$(OBJEXT) \
       ../src/fastppa/estimate$(OBJEXT) \
       ../src/fastppa/technology_db$(OBJEXT) \
       ../src/smvlang/smvlang$(LIBEXT) \
       ../src/temporal-logic/temporal-logic$(LIBEXT) \
       ../src/trans-netlist/trans-netlist$(LIBEXT) \
       ../src/trans-word-level/trans-word-level$(LIBEXT) \
       ../src/verilog/verilog$(LIBEXT)

ifneq ($(BUILD_ENV),MSVC)
SRC += new-ic3/ic3_solver.cpp
INCLUDES += -I ../src/ic3/minisat
OBJ += ../src/new-ic3/new-ic3$(LIBEXT) \
       ../src/ic3/minisat/build/release/lib/libminisat.a
endif

cprover.dir:
	$(MAKE) $(MAKEARGS) -C ../src

CPROVER_LIBS = $(CPROVER_DIR)/src/solvers/solvers$(LIBEXT) \
               $(CPROVER_DIR)/src/langapi/langapi$(LIBEXT) \
               $(CPROVER_DIR)/src/util/util$(LIBEXT) \
               $(CPROVER_DIR)/src/big-int/big-int$(LIBEXT) \
               # Empty last line

OBJ += $(CPROVER_LIBS)

all: test

test: unit_tests$(EXEEXT)
	./unit_tests$(EXEEXT)

###############################################################################

unit_tests$(EXEEXT): $(OBJ)
	$(LINKBIN)
