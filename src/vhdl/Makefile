SRC = vhdl_language.cpp expr2vhdl.cpp vhdl_y.tab.cpp vhdl_lex.yy.cpp \
      vhdl_parser.cpp vhdl_parse_tree.cpp vhdl_typecheck.cpp

include ../config.inc

INCLUDES= -I $(CBMC)/src

CLEANFILES = vhdl$(LIBEXT) vhdl_y.tab.cpp vhdl_y.tab.h vhdl_lex.yy.cpp y.output

all: vhdl$(LIBEXT)

###############################################################################

vhdl$(LIBEXT): $(OBJ)
	$(LINKLIB)

vhdl_y.tab.cpp: parser.y
	$(YACC) $(YFLAGS) $$flags -pyyvhdl -d parser.y -o $@

vhdl_y.tab.h: vhdl_y.tab.cpp
	if [ -e y.tab.hpp ] ; then mv y.tab.hpp $@ ; else \
        mv y.tab.cpp.h $@ ; fi

vhdl_lex.yy.cpp: scanner.l
	$(LEX) -i -Pyyvhdl -o$@ scanner.l

# extra dependencies
y.tab$(OBJEXT): y.tab.cpp y.tab.h
lex.yy$(OBJEXT): y.tab.cpp lex.yy.cpp y.tab.h

