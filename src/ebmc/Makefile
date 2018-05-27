SRC = \
      bdd_engine.cpp \
      cegar/abstract.cpp \
      cegar/bmc_cegar.cpp \
      cegar/latch_ordering.cpp \
      cegar/refine.cpp \
      cegar/simulate.cpp \
      cegar/verify.cpp \
      diameter.cpp \
      diatest.cpp \
      ebmc_base.cpp \
      ebmc_languages.cpp \
      ebmc_parse_options.cpp \
      ebmc_solvers.cpp \
      k_induction.cpp \
      main.cpp \
      negate_property.cpp \
      show_properties.cpp \
      show_trans.cpp \
      #empty line

OBJ+= $(CBMC)/src/util/util$(LIBEXT) \
      $(CBMC)/src/langapi/langapi$(LIBEXT) \
      $(CBMC)/src/ansi-c/string_constant$(OBJEXT) \
      $(CBMC)/src/util/c_types$(OBJEXT) \
      $(CBMC)/src/solvers/solvers$(LIBEXT) \
      $(CBMC)/src/big-int/big-int$(LIBEXT) \
      ../trans-netlist/trans-netlist$(LIBEXT) \
      ../trans-word-level/trans-word-level$(LIBEXT) \
      ../smvlang/smvlang$(LIBEXT) \
      ../aiger/aiger$(LIBEXT) \
      ../ic3/libic3$(LIBEXT)   

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

CXXFLAGS += -D'LOCAL_IREP_IDS=<hw_cbmc_irep_ids.h>'

LIBS = ../ic3/minisat/build/release/lib/libminisat.a

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
