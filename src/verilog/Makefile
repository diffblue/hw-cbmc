SRC = verilog_language.cpp verilog_y.tab.cpp verilog_lex.yy.cpp verilog_parser.cpp \
      expr2verilog.cpp verilog_typecheck.cpp verilog_preprocessor.cpp \
      verilog_typecheck_expr.cpp verilog_synthesis.cpp \
      verilog_interfaces.cpp verilog_typecheck_base.cpp \
      verilog_generate.cpp verilog_parameterize_module.cpp \
      verilog_symbol_table.cpp verilog_parse_tree.cpp \
      verilog_module.cpp vtype.cpp verilog_typecheck_type.cpp \
      verilog_interpreter.cpp

include $(CPROVER_DIR)/config.inc
include $(CPROVER_DIR)/common

INCLUDES= -I $(CPROVER_DIR) -I ..
CXXFLAGS += -D'LOCAL_IREP_IDS=<hw_cbmc_irep_ids.h>'

CLEANFILES = verilog$(LIBEXT) verilog_y.tab.h verilog_y.tab.cpp \
             verilog_lex.yy.cpp verilog_y.output

all: verilog$(LIBEXT)

###############################################################################

verilog$(LIBEXT): $(OBJ)
	$(LINKLIB)

verilog_y.tab.cpp: parser.y
	$(YACC) $(YFLAGS) $$flags -pyyverilog --defines=verilog_y.tab.h -d parser.y -o $@

verilog_y.tab.h: verilog_y.tab.cpp

verilog_lex.yy.cpp: scanner.l
	$(LEX) -Pyyverilog -o$@ scanner.l

# extra dependencies
verilog_y.tab$(OBJEXT): verilog_y.tab.cpp verilog_y.tab.h
verilog_lex.yy$(OBJEXT): verilog_y.tab.cpp verilog_lex.yy.cpp verilog_y.tab.h

