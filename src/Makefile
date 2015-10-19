SUBDIRS = ebmc hw-cbmc trans-word-level trans-netlist verilog vhdl smvlang

all: hw-cbmc ebmc

.PHONY: $(SUBDIRS)
.PHONY: clean

$(SUBDIRS):
	$(MAKE) -C $@

# Dependencies

ebmc: trans-word-level trans-netlist verilog vhdl smvlang

hw-cbmc: trans-word-level trans-netlist verilog vhdl smvlang

clean: $(patsubst %, %_clean, $(SUBDIRS))

$(patsubst %, %_clean, $(SUBDIRS)):
	if [ -e $(patsubst %_clean, %, $@)/. ] ; then \
	        $(MAKE) $(MAKEARGS) -C $(patsubst %_clean, %, $@) clean ; \
	fi

