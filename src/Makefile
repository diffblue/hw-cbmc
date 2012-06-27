SUBDIRS = ebmc hw-cbmc trans verilog vhdl

all: hw-cbmc ebmc

.PHONY: $(SUBDIRS)

$(SUBDIRS):
	$(MAKE) -C $@

# Dependencies

ebmc: trans verilog vhdl

hw-cbmc: trans verilog vhdl

