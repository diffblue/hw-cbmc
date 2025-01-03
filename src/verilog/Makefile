SRC = aval_bval_encoding.cpp \
      convert_literals.cpp \
      expr2verilog.cpp \
      sva_expr.cpp \
      verilog_bits.cpp \
      verilog_elaborate.cpp \
      verilog_elaborate_type.cpp \
      verilog_expr.cpp \
      verilog_generate.cpp \
      verilog_interfaces.cpp \
      verilog_interpreter.cpp \
      verilog_language.cpp \
      verilog_lex.yy.cpp \
      verilog_lowering.cpp \
      verilog_parameterize_module.cpp \
      verilog_parse_tree.cpp \
      verilog_parser.cpp \
      verilog_preprocessor.cpp \
      verilog_preprocessor_lex.yy.cpp \
      verilog_preprocessor_tokenizer.cpp \
      verilog_simplifier.cpp \
      verilog_standard.cpp \
      verilog_symbol_table.cpp \
      verilog_synthesis.cpp \
      verilog_typecheck.cpp \
      verilog_typecheck_base.cpp \
      verilog_typecheck_expr.cpp \
      verilog_typecheck_sva.cpp \
      verilog_types.cpp \
      verilog_y.tab.cpp \
      vtype.cpp

include ../config.inc
include ../common

CLEANFILES = verilog$(LIBEXT) verilog_y.tab.h verilog_y.tab.cpp \
             verilog_lex.yy.cpp verilog_y.output

all: verilog$(LIBEXT)

# override -Werror to silence expected warnings
YFLAGS += -Wno-error=other

###############################################################################

verilog$(LIBEXT): $(OBJ)
	$(LINKLIB)

verilog_y.tab.cpp: parser.y
	$(YACC) $(YFLAGS) $$flags -pyyverilog --defines=verilog_y.tab.h -d parser.y -o $@

verilog_y.tab.h: verilog_y.tab.cpp

verilog_lex.yy.cpp: scanner.l
	$(LEX) -Pyyverilog -o$@ scanner.l

verilog_preprocessor_lex.yy.cpp: verilog_preprocessor_tokenizer.l
	$(LEX) -Pyyverilog_preprocessor -o$@ verilog_preprocessor_tokenizer.l

# extra dependencies
verilog_y.tab$(OBJEXT): verilog_y.tab.cpp verilog_y.tab.h
verilog_lex.yy$(OBJEXT): verilog_y.tab.cpp verilog_lex.yy.cpp verilog_y.tab.h

