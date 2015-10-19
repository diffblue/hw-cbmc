SRC = bmc_map.cpp counterexample.cpp unwind.cpp property.cpp get_trans.cpp \
      instantiate.cpp word_level_trans.cpp netlist.cpp \
      var_map.cpp unwind_netlist.cpp ldg.cpp compute_ct.cpp \
      trans_trace.cpp show_modules.cpp netlist_trans.cpp \
      map_aigs.cpp bv_varid.cpp

include ../config.inc

INCLUDES= -I $(CBMC)/src

CLEANFILES = trans-netlist$(LIBEXT)

all: trans-netlist$(LIBEXT)

###############################################################################

trans-netlist$(LIBEXT): $(OBJ)
	$(LINKLIB)

