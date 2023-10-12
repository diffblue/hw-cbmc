SRC = aig.cpp aig_prop.cpp bmc_map.cpp counterexample_netlist.cpp \
      instantiate_netlist.cpp netlist.cpp trans_trace_netlist.cpp \
      var_map.cpp unwind_netlist.cpp ldg.cpp compute_ct.cpp \
      trans_trace.cpp trans_to_netlist.cpp \
      map_aigs.cpp bv_varid.cpp

include ../config.inc
include ../common

CLEANFILES = trans-netlist$(LIBEXT)

all: trans-netlist$(LIBEXT)

###############################################################################

trans-netlist$(LIBEXT): $(OBJ)
	$(LINKLIB)

