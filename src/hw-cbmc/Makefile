SRC = main.cpp parseoptions.cpp hw_bmc.cpp next_timeframe.cpp \
      map_vars.cpp gen_interface.cpp set_inputs.cpp

OBJ+= $(CBMC)/src/cbmc/parseoptions$(OBJEXT) \
      $(CBMC)/src/cbmc/xml_interface$(OBJEXT) \
      $(CBMC)/src/cbmc/languages$(OBJEXT) \
      $(CBMC)/src/cbmc/bmc$(OBJEXT) \
      $(CBMC)/src/cbmc/bv_cbmc$(OBJEXT) \
      $(CBMC)/src/cbmc/symex_bmc$(OBJEXT) \
      $(CBMC)/src/cbmc/counterexample_beautification$(OBJEXT) \
      $(CBMC)/src/cbmc/cbmc_solvers$(OBJEXT) \
      $(CBMC)/src/cbmc/show_vcc$(OBJEXT) \
      $(CBMC)/src/cbmc/cover$(OBJEXT) \
      $(CBMC)/src/cbmc/dimacs$(OBJEXT) \
      $(CBMC)/src/ansi-c/ansi-c$(LIBEXT) \
      $(CBMC)/src/linking/linking$(LIBEXT) \
      $(CBMC)/src/xmllang/xmllang$(LIBEXT) \
      $(CBMC)/src/big-int/bigint$(OBJEXT) \
      $(CBMC)/src/goto-symex/goto-symex$(LIBEXT) \
      $(CBMC)/src/goto-programs/goto-programs$(LIBEXT) \
      $(CBMC)/src/pointer-analysis/pointer-analysis$(LIBEXT) \
      $(CBMC)/src/langapi/langapi$(LIBEXT) \
      $(CBMC)/src/solvers/solvers$(LIBEXT) \
      $(CBMC)/src/util/util$(LIBEXT) \
      ../trans/trans$(LIBEXT)

include ../config.inc

INCLUDES= -I $(CBMC)/src -I $(CBMC)/src/util -I ..

LIBS =

all: hw-cbmc$(EXEEXT)

ifneq ($(wildcard $(CBMC)/src/bv_refinement/Makefile),)
  OBJ += $(CBMC)/src/bv_refinement/bv_refinement$(LIBEXT)
  CXXFLAGS += -DHAVE_BV_REFINEMENT
endif

ifneq ($(wildcard $(CBMC)/src/cpp/Makefile),)
  OBJ += $(CBMC)/src/cpp/cpp$(LIBEXT)
  CXXFLAGS += -DHAVE_CPP
endif

ifneq ($(wildcard $(CBMC)/src/specc/Makefile),)
  OBJ += $(CBMC)/src/specc/specc$(LIBEXT)
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
