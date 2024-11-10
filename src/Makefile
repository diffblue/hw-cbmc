DIRS = ebmc hw-cbmc temporal-logic trans-word-level trans-netlist \
       verilog vhdl smvlang ic3 aiger vlindex

CPROVER_DIR:=../lib/cbmc/src

all: hw-cbmc.dir ebmc.dir vlindex.dir

.PHONY: $(patsubst %, %.dir, $(DIRS))
$(patsubst %, %.dir, $(DIRS)):
	## Entering $(basename $@)
	$(MAKE) $(MAKEARGS) -C $(basename $@)

# Dependencies

vhdl.dir: cprover.dir

ebmc.dir: trans-word-level.dir trans-netlist.dir verilog.dir vhdl.dir \
      smvlang.dir aiger.dir temporal-logic.dir cprover.dir

ifneq ($(BUILD_ENV),MSVC)
ebmc.dir: ic3.dir
endif

hw-cbmc.dir: trans-word-level.dir trans-netlist.dir verilog.dir \
         vhdl.dir smvlang.dir cprover.dir temporal-logic.dir

vlindex.dir: cprover.dir verilog.dir

# building cbmc proper
.PHONY: cprover.dir
cprover.dir:
	$(MAKE) $(MAKEARGS) -C $(CPROVER_DIR) \
  CP_EXTRA_CXXFLAGS='-I ../../../../src -DLOCAL_IREP_IDS=\<hw_cbmc_irep_ids.h\>' \
  cbmc.dir

.PHONY: clean
clean: $(patsubst %, %_clean, $(DIRS)) cprover_clean

.PHONY: $(patsubst %, %_clean, $(DIRS))
$(patsubst %, %_clean, $(DIRS)):
	if [ -e $(patsubst %_clean, %, $@)/. ] ; then \
	        $(MAKE) $(MAKEARGS) -C $(patsubst %_clean, %, $@) clean ; \
	fi

.PHONY: cprover_clean
cprover_clean:
	$(MAKE) $(MAKEARGS) -C $(CPROVER_DIR) clean
