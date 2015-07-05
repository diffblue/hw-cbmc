SRC = verilog_language.cpp verilog_y.tab.cpp verilog_lex.yy.cpp verilog_parser.cpp \
      expr2verilog.cpp verilog_typecheck.cpp verilog_preprocessor.cpp \
      verilog_typecheck_expr.cpp verilog_synthesis.cpp \
      verilog_interfaces.cpp verilog_typecheck_base.cpp \
      verilog_generate.cpp verilog_parameterize_module.cpp \
      verilog_context.cpp verilog_parse_tree.cpp \
      verilog_module.cpp vtype.cpp verilog_typecheck_type.cpp

include ../config.inc

INCLUDES= -I $(CBMC)/src

CLEANFILES = verilog$(LIBEXT) verilog_y.tab.h verilog_y.tab.cpp \
             verilog_lex.yy.cpp verilog_y.output

all: verilog$(LIBEXT)

###############################################################################

verilog$(LIBEXT): $(OBJ)
	$(LINKLIB)

verilog_y.tab.cpp: parser.y
	$(YACC) $(YFLAGS) $$flags -pyyverilog -d parser.y -o $@

verilog_y.tab.h: verilog_y.tab.cpp
	if [ -e verilog_y.tab.hpp ] ; then mv verilog_y.tab.hpp verilog_y.tab.h ; else \
        mv y.tab.cpp.h y.tab.h ; fi

verilog_lex.yy.cpp: scanner.l
	$(LEX) -Pyyverilog -o$@ scanner.l

# extra dependencies
verilog_y.tab$(OBJEXT): verilog_y.tab.cpp verilog_y.tab.h
verilog_lex.yy$(OBJEXT): verilog_y.tab.cpp verilog_lex.yy.cpp verilog_y.tab.h

