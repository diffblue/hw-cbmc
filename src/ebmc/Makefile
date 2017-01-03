SRC = diameter.cpp main.cpp diatest.cpp show_properties.cpp \
      k_induction.cpp ebmc_base.cpp ebmc_solvers.cpp bdd_engine.cpp \
      ebmc_parse_options.cpp show_trans.cpp ebmc_languages.cpp \
      negate_property.cpp \
      cegar/bmc_cegar.cpp cegar/latch_ordering.cpp \
      cegar/verify.cpp cegar/abstract.cpp cegar/refine.cpp \
      cegar/simulate.cpp

OBJ+= $(CBMC)/src/util/util$(LIBEXT) \
      $(CBMC)/src/langapi/langapi$(LIBEXT) \
      $(CBMC)/src/ansi-c/string_constant$(OBJEXT) \
      $(CBMC)/src/ansi-c/c_types$(OBJEXT) \
      $(CBMC)/src/solvers/solvers$(LIBEXT) \
      $(CBMC)/src/big-int/big-int$(LIBEXT) \
      ../trans-netlist/trans-netlist$(LIBEXT) \
      ../trans-word-level/trans-word-level$(LIBEXT) \
      ../smvlang/smvlang$(LIBEXT) \
      ../aiger/aiger$(LIBEXT)

ifdef MODULE_INTERPOLATION
  CXXFLAGS += -DHAVE_INTERPOLATION
  OBJ += ../interpolation/interpolation$(LIBEXT)
  SRC += interpolation/interpolation_expr.cpp \
	 interpolation/interpolation_netlist.cpp \
	 interpolation/interpolation_netlist_vmcai.cpp \
         interpolation/compute-interpolant.cpp \
         coverage/coverage.cpp coverage/interpolation_coverage.cpp \
         coverage/assumptions.cpp coverage/induction_coverage.cpp \
         coverage/core.cpp
endif

ifneq ($(wildcard ../verilog/Makefile),)
  OBJ += ../verilog/verilog$(LIBEXT)
  SRC += output_verilog.cpp
  CXXFLAGS += -DHAVE_VERILOG
endif

ifneq ($(wildcard ../vhdl/Makefile),)
  OBJ += ../vhdl/vhdl$(LIBEXT)
  CXXFLAGS += -DHAVE_VHDL
endif

include ../config.inc

INCLUDES= -I .. -I $(CBMC)/src

LIBS =

CLEANFILES = ebmc$(EXEEXT)

all: ebmc$(EXEEXT)

ifdef HYPER_RESOLUTION
CXXFLAGS += -DHYPER
endif

ifdef DEBUG
CXXFLAGS += -DDEBUG
endif

###############################################################################

ebmc$(EXEEXT): $(OBJ)
	$(LINKBIN)
