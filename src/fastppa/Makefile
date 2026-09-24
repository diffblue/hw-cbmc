SRC = \
      estimate.cpp \
      main.cpp \
      fastppa_estimator.cpp \
      fastppa_frontend.cpp \
      fastppa_parse_options.cpp \
      technology_db.cpp \
      #empty line

OBJ+= $(CPROVER_DIR)/util/util$(LIBEXT) \
      $(CPROVER_DIR)/big-int/big-int$(LIBEXT) \
      $(CPROVER_DIR)/langapi/langapi$(LIBEXT) \
      $(CPROVER_DIR)/solvers/solvers$(LIBEXT) \
      ../temporal-logic/temporal-logic$(LIBEXT) \
      ../trans-netlist/trans-netlist$(LIBEXT) \
      ../trans-word-level/trans-word-level$(LIBEXT) \
      ../aiger/aiger$(LIBEXT) \
      ../smvlang/smvlang$(LIBEXT) \
      ../verilog/verilog$(LIBEXT) \
      ../ebmc/transition_system$(OBJEXT) \
      ../ebmc/ebmc_language$(OBJEXT) \
      ../ebmc/show_modules$(OBJEXT)

include ../config.inc
include ../common

CLEANFILES = fastppa$(EXEEXT)

all: fastppa$(EXEEXT)

###############################################################################

fastppa$(EXEEXT): $(OBJ)
	$(LINKBIN)
