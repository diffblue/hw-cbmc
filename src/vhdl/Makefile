SRC = vhdl_language.cpp expr2vhdl.cpp y.tab.cpp lex.yy.cpp \
      vhdl_parser.cpp vhdl_parse_tree.cpp vhdl_typecheck.cpp \
      vhdl_convert.cpp

include ../config.inc

INCLUDES= -I $(CBMC)/src

CLEANFILES = vhdl$(LIBEXT) y.tab.cpp y.tab.h lex.yy.cpp y.output

all: vhdl$(LIBEXT)

###############################################################################

vhdl$(LIBEXT): $(OBJ)
	$(LINKLIB)

y.tab.cpp: parser.y
	$(YACC) $(YFLAGS) $$flags -pyyvhdl -d parser.y -o y.tab.cpp

y.tab.h: y.tab.cpp
	if [ -e y.tab.hpp ] ; then mv y.tab.hpp y.tab.h ; else \
        mv y.tab.cpp.h y.tab.h ; fi

lex.yy.cpp: scanner.l
	$(LEX) -i -Pyyvhdl -o$@ scanner.l

# extra dependencies
y.tab$(OBJEXT): y.tab.cpp y.tab.h
lex.yy$(OBJEXT): y.tab.cpp lex.yy.cpp y.tab.h

