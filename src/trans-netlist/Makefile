SRC = aig.cpp \
      aig_prop.cpp \
      aig_terminals.cpp \
      bmc_map.cpp \
      build_netlist_var_map.cpp \
      bv_varid.cpp \
      compute_ct.cpp \
      counterexample_netlist.cpp \
      instantiate_netlist.cpp \
      ldg.cpp \
      map_aigs.cpp \
      netlist.cpp \
      netlist_boolbv.cpp \
      smv_netlist.cpp \
      trans_to_netlist.cpp \
      trans_trace.cpp \
      trans_trace_netlist.cpp \
      unwind_netlist.cpp \
      var_map.cpp \
      # last line

include ../config.inc
include ../common

CLEANFILES = trans-netlist$(LIBEXT)

all: trans-netlist$(LIBEXT)

###############################################################################

trans-netlist$(LIBEXT): $(OBJ)
	$(LINKLIB)

