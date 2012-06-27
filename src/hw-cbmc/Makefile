SRC = main.cpp parseoptions.cpp hw_bmc.cpp next_timeframe.cpp \
      map_vars.cpp gen_interface.cpp set_inputs.cpp

OBJ+= ../cbmc/parseoptions$(OBJEXT) \
      ../cbmc/xml_interface$(OBJEXT) \
      ../cbmc/languages$(OBJEXT) \
      ../cbmc/bmc$(OBJEXT) \
      ../cbmc/bv_cbmc$(OBJEXT) \
      ../cbmc/symex_bmc$(OBJEXT) \
      ../cbmc/counterexample_beautification$(OBJEXT) \
      ../cbmc/counterexample_beautification_pbs$(OBJEXT) \
      ../cbmc/counterexample_beautification_greedy$(OBJEXT) \
      ../cbmc/cbmc_solvers$(OBJEXT) \
      ../cbmc/show_vcc$(OBJEXT) \
      ../cbmc/cover$(OBJEXT) \
      ../cbmc/dimacs$(OBJEXT) \
      ../ansi-c/ansi-c$(LIBEXT) \
      ../xmllang/xmllang$(LIBEXT) \
      ../big-int/bigint$(OBJEXT) \
      ../goto-symex/goto-symex$(LIBEXT) \
      ../goto-programs/goto-programs$(LIBEXT) \
      ../pointer-analysis/pointer-analysis$(LIBEXT) \
      ../langapi/langapi$(LIBEXT) \
      ../solvers/solvers$(LIBEXT) \
      ../util/util$(LIBEXT) \
      ../trans/trans$(LIBEXT)

INCLUDES= -I ../$(CHAFF) -I .. -I ../util

LIBS =

include ../config.inc
include ../common

all: hw-cbmc$(EXEEXT)

ifneq ($(wildcard ../bv_refinement/Makefile),)
  OBJ += ../bv_refinement/bv_refinement$(LIBEXT)
  CXXFLAGS += -DHAVE_BV_REFINEMENT
endif

ifneq ($(wildcard ../cpp/Makefile),)
  OBJ += ../cpp/cpp$(LIBEXT)
  CXXFLAGS += -DHAVE_CPP
endif

ifneq ($(wildcard ../specc/Makefile),)
  OBJ += ../specc/specc$(LIBEXT)
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
