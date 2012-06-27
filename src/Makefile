SUBDIRS = ebmc hw-cbmc trans verilog vhdl smvlang

all: hw-cbmc ebmc

.PHONY: $(SUBDIRS)

$(SUBDIRS):
	$(MAKE) -C $@

# Dependencies

ebmc: trans verilog vhdl smvlang

hw-cbmc: trans verilog vhdl smvlang

