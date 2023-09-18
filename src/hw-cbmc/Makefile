SRC = hw_cbmc_main.cpp hw_cbmc_parse_options.cpp next_timeframe.cpp \
      map_vars.cpp gen_interface.cpp set_inputs.cpp hw_cbmc_languages.cpp \
      $(CPROVER_DIR)/cbmc/c_test_input_generator.cpp

OBJ+= $(CPROVER_DIR)/goto-checker/goto-checker$(LIBEXT) \
      $(CPROVER_DIR)/cbmc/cbmc_parse_options$(OBJEXT) \
      $(CPROVER_DIR)/goto-instrument/cover$(OBJEXT) \
      $(CPROVER_DIR)/goto-instrument/cover_basic_blocks$(OBJEXT) \
      $(CPROVER_DIR)/goto-instrument/cover_instrument_assume$(OBJEXT) \
      $(CPROVER_DIR)/goto-instrument/cover_instrument_other$(OBJEXT) \
      $(CPROVER_DIR)/goto-instrument/cover_instrument_mcdc$(OBJEXT) \
      $(CPROVER_DIR)/goto-instrument/cover_instrument_decision$(OBJEXT) \
      $(CPROVER_DIR)/goto-instrument/cover_instrument_condition$(OBJEXT) \
      $(CPROVER_DIR)/goto-instrument/cover_instrument_branch$(OBJEXT) \
      $(CPROVER_DIR)/goto-instrument/cover_instrument_location$(OBJEXT) \
      $(CPROVER_DIR)/goto-instrument/cover_util$(OBJEXT) \
      $(CPROVER_DIR)/goto-instrument/cover_filter$(OBJEXT) \
      $(CPROVER_DIR)/goto-instrument/full_slicer$(OBJEXT) \
      $(CPROVER_DIR)/goto-instrument/source_lines$(OBJEXT) \
      $(CPROVER_DIR)/goto-instrument/reachability_slicer$(OBJEXT) \
      $(CPROVER_DIR)/goto-instrument/nondet_static$(OBJEXT) \
      $(CPROVER_DIR)/goto-instrument/unwindset$(OBJEXT) \
      $(CPROVER_DIR)/xmllang/xml_interface$(OBJEXT) \
      $(CPROVER_DIR)/ansi-c/ansi-c$(LIBEXT) \
      $(CPROVER_DIR)/cpp/cpp$(LIBEXT) \
      $(CPROVER_DIR)/assembler/assembler$(LIBEXT) \
      $(CPROVER_DIR)/linking/linking$(LIBEXT) \
      $(CPROVER_DIR)/xmllang/xmllang$(LIBEXT) \
      $(CPROVER_DIR)/big-int/big-int$(LIBEXT) \
      $(CPROVER_DIR)/goto-symex/goto-symex$(LIBEXT) \
      $(CPROVER_DIR)/goto-programs/goto-programs$(LIBEXT) \
      $(CPROVER_DIR)/pointer-analysis/pointer-analysis$(LIBEXT) \
      $(CPROVER_DIR)/analyses/analyses$(LIBEXT) \
      $(CPROVER_DIR)/langapi/langapi$(LIBEXT) \
      $(CPROVER_DIR)/solvers/solvers$(LIBEXT) \
      $(CPROVER_DIR)/util/util$(LIBEXT) \
      $(CPROVER_DIR)/json/json$(LIBEXT) \
      ../trans-netlist/trans_trace$(OBJEXT) \
      ../trans-word-level/trans-word-level$(LIBEXT)

include ../config.inc

INCLUDES= -I $(CPROVER_DIR) -I ..

CXXFLAGS += -D'LOCAL_IREP_IDS=<hw_cbmc_irep_ids.h>'

LIBS =

CLEANFILES = hw-cbmc$(EXEEXT)

all: hw-cbmc$(EXEEXT)

ifneq ($(wildcard $(CPROVER_DIR)/bv_refinement/Makefile),)
  OBJ += $(CPROVER_DIR)/bv_refinement/bv_refinement$(LIBEXT)
  CXXFLAGS += -DHAVE_BV_REFINEMENT
endif

ifneq ($(wildcard $(CPROVER_DIR)/specc/Makefile),)
  OBJ += $(CPROVER_DIR)/specc/specc$(LIBEXT)
  CXXFLAGS += -DHAVE_SPECC
endif

ifneq ($(wildcard ../verilog/Makefile),)
  OBJ += ../verilog/verilog$(LIBEXT)
  CXXFLAGS += -DHAVE_VERILOG
endif

ifneq ($(wildcard ../vhdl/Makefile),)
  OBJ += ../vhdl/vhdl$(LIBEXT)
  CXXFLAGS += -DHAVE_VHDL
endif

ifneq ($(wildcard ../smvlang/Makefile),)
  OBJ += ../smvlang/smvlang$(LIBEXT)
  CXXFLAGS += -DHAVE_SMV
endif

ifneq ($(wildcard ../netlist/Makefile),)
  OBJ += ../netlist/netlist$(LIBEXT)
  CXXFLAGS += -DHAVE_NETLIST
endif

###############################################################################

hw-cbmc$(EXEEXT): $(OBJ)
	$(LINKBIN)

.PHONY: hw-cbmc-mac-signed

hw-cbmc-mac-signed: hw-cbmc$(EXEEXT)
	strip hw-cbmc$(EXEEXT) ; codesign -v -s $(OSX_IDENTITY) hw-cbmc$(EXEEXT)
