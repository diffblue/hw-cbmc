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
      dimacs_writer.cpp \
      ebmc_base.cpp \
      ebmc_languages.cpp \
      ebmc_parse_options.cpp \
      ebmc_properties.cpp \
      ebmc_solver_factory.cpp \
      k_induction.cpp \
      liveness_to_safety.cpp \
      main.cpp \
      negate_property.cpp \
      neural_liveness.cpp \
      random_traces.cpp \
      ranking_function.cpp \
      report_results.cpp \
      show_formula_solver.cpp \
      show_properties.cpp \
      show_trans.cpp \
      transition_system.cpp \
      waveform.cpp \
      #empty line

OBJ+= $(CPROVER_DIR)/util/util$(LIBEXT) \
      $(CPROVER_DIR)/langapi/langapi$(LIBEXT) \
      $(CPROVER_DIR)/goto-programs/system_library_symbols$(OBJEXT) \
      $(CPROVER_DIR)/solvers/solvers$(LIBEXT) \
      $(CPROVER_DIR)/big-int/big-int$(LIBEXT) \
      $(CPROVER_DIR)/util/c_types$(OBJEXT) \
      $(CPROVER_DIR)/goto-programs/xml_expr$(OBJEXT) \
      ../trans-netlist/trans-netlist$(LIBEXT) \
      ../trans-word-level/trans-word-level$(LIBEXT) \
      ../smvlang/smvlang$(LIBEXT) \
      ../aiger/aiger$(LIBEXT) \
      ../ic3/libic3$(LIBEXT) \
      ../trans-netlist/aig$(OBJEXT) \
      ../trans-netlist/aig_prop$(OBJEXT)

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
include ../common

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
