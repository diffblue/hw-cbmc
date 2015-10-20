SRC = bmc_map.cpp counterexample.cpp property_netlist.cpp \
      instantiate.cpp netlist.cpp \
      var_map.cpp unwind_netlist.cpp ldg.cpp compute_ct.cpp \
      trans_trace.cpp netlist_trans.cpp \
      map_aigs.cpp bv_varid.cpp

include ../config.inc

INCLUDES= -I $(CBMC)/src

CLEANFILES = trans-netlist$(LIBEXT)

all: trans-netlist$(LIBEXT)

###############################################################################

trans-netlist$(LIBEXT): $(OBJ)
	$(LINKLIB)

