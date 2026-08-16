SRC = \
      vl_simulator.cpp \
      vlsim_main.cpp \
      vlsim_parse_options.cpp \
      #empty line

OBJ+= $(CPROVER_DIR)/util/util$(LIBEXT) \
      $(CPROVER_DIR)/langapi/langapi$(LIBEXT) \
      $(CPROVER_DIR)/big-int/big-int$(LIBEXT) \
      ../ebmc/ebmc_language$(OBJEXT) \
      ../ebmc/ebmc_version$(OBJEXT) \
      ../ebmc/show_modules$(OBJEXT) \
      ../ebmc/transition_system$(OBJEXT) \
      ../temporal-logic/temporal-logic$(LIBEXT) \
      ../trans-word-level/trans-word-level$(LIBEXT) \
      ../verilog/verilog$(LIBEXT)

include ../config.inc
include ../common

CLEANFILES = vlsim$(EXEEXT)

all: vlsim$(EXEEXT)

ifdef DEBUG
CXXFLAGS += -DDEBUG
endif

###############################################################################

vlsim$(EXEEXT): $(OBJ)
	$(LINKBIN)
