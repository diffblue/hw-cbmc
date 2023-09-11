SRC = vhdl_language.cpp expr2vhdl.cpp vhdl_y.tab.cpp vhdl_lex.yy.cpp \
      vhdl_parser.cpp vhdl_parse_tree.cpp vhdl_typecheck.cpp \
      vhdl_synthesis.cpp vhdl_std_packages.cpp vhdl_libraries.cpp

include $(CPROVER_DIR)/config.inc
include $(CPROVER_DIR)/common

INCLUDES= -I $(CPROVER_DIR) -I ..
CXXFLAGS += -D'LOCAL_IREP_IDS=<hw_cbmc_irep_ids.h>'

CLEANFILES = vhdl$(LIBEXT) vhdl_y.tab.cpp vhdl_y.tab.h vhdl_lex.yy.cpp vhdl_y.output

all: vhdl$(LIBEXT)

###############################################################################

vhdl$(LIBEXT): $(OBJ)
	$(LINKLIB)

vhdl_y.tab.cpp: parser.y
	$(YACC) $(YFLAGS) $$flags -pyyvhdl --defines=vhdl_y.tab.h -d parser.y -o $@

vhdl_y.tab.h: vhdl_y.tab.cpp

vhdl_lex.yy.cpp: scanner.l
	$(LEX) -i -Pyyvhdl -o$@ scanner.l

# extra dependencies
vhdl_y.tab$(OBJEXT): vhdl_y.tab.cpp vhdl_y.tab.h
vhdl_lex.yy$(OBJEXT): vhdl_y.tab.cpp vhdl_lex.yy.cpp vhdl_y.tab.h

# libraries

library_standard.inc: libraries/standard.vhdl
	$(CPROVER_DIR)/ansi-c/file_converter$(EXEEXT) < $< > $@

vhdl_libraries.cpp: library_standard.inc


