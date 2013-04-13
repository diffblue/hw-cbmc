SRC = diameter.cpp main.cpp diatest.cpp show_claims.cpp \
      k_induction.cpp ebmc_base.cpp ebmc_solvers.cpp \
      parseoptions.cpp  show_trans.cpp  \
      languages.cpp \
      cegar/bmc_cegar.cpp cegar/latch_ordering.cpp \
      cegar/verify.cpp cegar/abstract.cpp cegar/refine.cpp \
      cegar/simulate.cpp       

OBJ+= $(CBMC)/src/util/util$(LIBEXT) \
      $(CBMC)/src/langapi/langapi$(LIBEXT) \
      $(CBMC)/src/ansi-c/ansi-c$(LIBEXT) \
      $(CBMC)/src/linking/linking$(LIBEXT) \
      $(CBMC)/src/solvers/solvers$(LIBEXT) \
      $(CBMC)/src/big-int/bigint$(OBJEXT) \
      ../trans/trans$(LIBEXT) \
      ../smvlang/smvlang$(LIBEXT)      

include ../config.inc

INCLUDES= -I .. -I $(CBMC)/src

LIBS =

all: ebmc$(EXEEXT)

ifdef HYPER_RESOLUTION
CXXFLAGS += -DHYPER
endif

ifdef DEBUG
CXXFLAGS += -DDEBUG
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

#ifneq ($(wildcard ../prover/Makefile),)
#  CXXFLAGS += -DHAVE_PROVER
#  OBJ += ../prover/prover$(LIBEXT)
#endif

ifneq ($(wildcard ../verilog/Makefile),)
  OBJ += ../verilog/verilog$(LIBEXT)
  SRC += output_verilog.cpp
  CXXFLAGS += -DHAVE_VERILOG
endif

ifneq ($(wildcard ../vhdl/Makefile),)
  OBJ += ../vhdl/vhdl$(LIBEXT)
  CXXFLAGS += -DHAVE_VHDL
endif

ifneq ($(wildcard ../netlist/Makefile),)
  OBJ += ../netlist/netlist$(LIBEXT)
  CXXFLAGS += -DHAVE_NETLIST
endif

###############################################################################

ebmc$(EXEEXT): $(OBJ)
	$(CXX) $(LINKFLAGS) -o $@ $(OBJ) $(LIBS)
