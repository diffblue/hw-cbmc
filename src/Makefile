SUBDIRS = ebmc hw-cbmc trans-word-level trans-netlist verilog vhdl smvlang ic3 aiger cprover

CPROVER_DIR = lib/cbmc/src
export CPROVER_DIR

all: hw-cbmc ebmc

.PHONY: $(SUBDIRS)
.PHONY: clean

$(SUBDIRS):
	$(MAKE) -C $@

# Dependencies

ebmc: trans-word-level trans-netlist verilog vhdl smvlang ic3 aiger cprover

hw-cbmc: trans-word-level trans-netlist verilog vhdl smvlang cprover

# building cbmc proper
.PHONY: cprover.dir
cprover:
	$(MAKE) $(MAKEARGS) -C ../$(CPROVER_DIR)

clean: $(patsubst %, %_clean, $(SUBDIRS))

$(patsubst %, %_clean, $(SUBDIRS)):
	if [ -e $(patsubst %_clean, %, $@)/. ] ; then \
	        $(MAKE) $(MAKEARGS) -C $(patsubst %_clean, %, $@) clean ; \
	fi

