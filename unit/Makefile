.PHONY: test

# Main
SRC = unit_tests.cpp

# Test source files
SRC += smvlang/expr2smv.cpp \
       temporal-logic/hoa.cpp \
       temporal-logic/ltl_sva_to_string.cpp \
       temporal-logic/rewrite_sva_sequence.cpp \
       temporal-logic/sva_sequence_match.cpp \
       temporal-logic/sva_to_ltl.cpp \
       temporal-logic/nnf.cpp \
       temporal-logic/trivial_sva.cpp \
       trans-netlist/aig.cpp \
       verilog/typename.cpp \
       # Empty last line

INCLUDES= -I ../src/ -I . -I $(CPROVER_DIR)/unit -I $(CPROVER_DIR)/src

CPROVER_DIR = ../lib/cbmc

include $(CPROVER_DIR)/src/config.inc
include $(CPROVER_DIR)/src/common

CXXFLAGS += -D'LOCAL_IREP_IDS=<hw_cbmc_irep_ids.h>'

OBJ += ../src/smvlang/smvlang$(LIBEXT) \
       ../src/temporal-logic/temporal-logic$(LIBEXT) \
       ../src/trans-netlist/trans-netlist$(LIBEXT) \
       ../src/verilog/verilog$(LIBEXT)

cprover.dir:
	$(MAKE) $(MAKEARGS) -C ../src

CPROVER_LIBS = $(CPROVER_DIR)/src/solvers/solvers$(LIBEXT) \
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
