SRC = verilog_language.cpp y.tab.cpp lex.yy.cpp verilog_parser.cpp \
      expr2verilog.cpp verilog_typecheck.cpp verilog_preprocessor.cpp \
      verilog_typecheck_expr.cpp verilog_synthesis.cpp \
      verilog_interfaces.cpp verilog_typecheck_base.cpp \
      verilog_generate.cpp verilog_module_instance.cpp \
      verilog_context.cpp verilog_parse_tree.cpp \
      verilog_flattening.cpp verilog_module.cpp vtype.cpp

INCLUDES= -I .. -I ../util

include ../config.inc
include ../common

all: verilog$(LIBEXT)

###############################################################################

verilog$(LIBEXT): $(OBJ)
	$(LINKLIB)

y.tab.cpp: parser.y
	$(YACC) $(YFLAGS) $$flags -pyyverilog -d parser.y -o y.tab.cpp

y.tab.h: y.tab.cpp
	if [ -e y.tab.hpp ] ; then mv y.tab.hpp y.tab.h ; else \
        mv y.tab.cpp.h y.tab.h ; fi

lex.yy.cpp: scanner.l
	$(LEX) -Pyyverilog -o$@ scanner.l

# extra dependencies
y.tab$(OBJEXT): y.tab.cpp y.tab.h
lex.yy$(OBJEXT): y.tab.cpp lex.yy.cpp y.tab.h

