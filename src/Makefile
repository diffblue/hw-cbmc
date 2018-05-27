SUBDIRS = ebmc hw-cbmc trans-word-level trans-netlist verilog vhdl smvlang ic3 aiger

CPROVER_DIR = lib/cbmc/src
export CPROVER_DIR

all: hw-cbmc ebmc

.PHONY: $(SUBDIRS)
.PHONY: clean

$(SUBDIRS):
	$(MAKE) -C $@

# Dependencies

ebmc: trans-word-level trans-netlist verilog vhdl smvlang ic3 aiger cprover.dir

hw-cbmc: trans-word-level trans-netlist verilog vhdl smvlang cprover.dir

# building cbmc proper
.PHONY: cprover.dir
cprover.dir:
	$(MAKE) $(MAKEARGS) -C ../$(CPROVER_DIR) \
	CXXFLAGS='-D"LOCAL_IREP_IDS=<../../../src/hw_cbmc_irep_ids.h>" -Wall -pedantic -Werror -Wno-deprecated-declarations'

clean: $(patsubst %, %_clean, $(SUBDIRS))

$(patsubst %, %_clean, $(SUBDIRS)):
	if [ -e $(patsubst %_clean, %, $@)/. ] ; then \
	        $(MAKE) $(MAKEARGS) -C $(patsubst %_clean, %, $@) clean ; \
	fi

