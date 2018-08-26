DIRS = ebmc hw-cbmc trans-word-level trans-netlist verilog vhdl smvlang ic3 aiger

CPROVER_DIR = lib/cbmc/src
export CPROVER_DIR

all: hw-cbmc.dir ebmc.dir

.PHONY: clean

$(patsubst %, %.dir, $(DIRS)):
	## Entering $(basename $@)
	$(MAKE) $(MAKEARGS) -C $(basename $@)

# Dependencies

ebmc.dir: trans-word-level.dir trans-netlist.dir verilog.dir vhdl.dir \
      smvlang.dir ic3.dir aiger.dir cprover.dir

hw-cbmc.dir: trans-word-level.dir trans-netlist.dir verilog.dir \
         vhdl.dir smvlang.dir cprover.dir

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

