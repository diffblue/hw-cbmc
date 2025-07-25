SRC = \
      bdd_engine.cpp \
      bmc.cpp \
      cegar/abstract.cpp \
      cegar/bmc_cegar.cpp \
      cegar/latch_ordering.cpp \
      cegar/refine.cpp \
      cegar/simulate.cpp \
      cegar/verify.cpp \
      completeness_threshold.cpp \
      diameter.cpp \
      diatest.cpp \
      dimacs_writer.cpp \
      ebmc_base.cpp \
      ebmc_languages.cpp \
      ebmc_parse_options.cpp \
      ebmc_properties.cpp \
      ebmc_solver_factory.cpp \
      ebmc_version.cpp \
      format_hooks.cpp \
      instrument_past.cpp \
      instrument_buechi.cpp \
      k_induction.cpp \
      liveness_to_safety.cpp \
      live_signal.cpp \
      main.cpp \
      netlist.cpp \
      neural_liveness.cpp \
      output_file.cpp \
      output_smv_word_level.cpp \
      output_verilog.cpp \
      property_checker.cpp \
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
      $(CPROVER_DIR)/big-int/big-int$(LIBEXT) \
      $(CPROVER_DIR)/langapi/langapi$(LIBEXT) \
      $(CPROVER_DIR)/goto-programs/xml_expr$(OBJEXT) \
      $(CPROVER_DIR)/solvers/solvers$(LIBEXT) \
      ../temporal-logic/temporal-logic$(LIBEXT) \
      ../trans-netlist/trans-netlist$(LIBEXT) \
      ../trans-word-level/trans-word-level$(LIBEXT) \
      ../aiger/aiger$(LIBEXT) \
      ../smvlang/smvlang$(LIBEXT) \
      ../verilog/verilog$(LIBEXT)

ifneq ($(BUILD_ENV),MSVC)
OBJ += ../ic3/libic3$(LIBEXT)
OBJ += ../ic3/minisat/build/release/lib/libminisat.a
endif

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

include ../config.inc
include ../common

# get version from git
GIT_INFO = $(shell git describe --tags --always --dirty || echo "n/a")
RELEASE_INFO = const char *EBMC_VERSION="$(EBMC_VERSION) ($(GIT_INFO))";
GIT_INFO_FILE = ebmc_version.cpp

$(GIT_INFO_FILE):
	echo '$(RELEASE_INFO)' > $@

# mark the actually generated file as a phony target to enforce a rebuild - but
# only if the version information has changed!
KNOWN_RELEASE_INFO = $(shell cat $(GIT_INFO_FILE) 2>/dev/null)
ifneq ($(RELEASE_INFO), $(KNOWN_RELEASE_INFO))
.PHONY: $(GIT_INFO_FILE)
endif

ifneq ($(wildcard ../vhdl/Makefile),)
  OBJ += ../vhdl/vhdl$(LIBEXT)
  CXXFLAGS += -DHAVE_VHDL
endif

CLEANFILES = $(GIT_INFO_FILE) ebmc$(EXEEXT)

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
