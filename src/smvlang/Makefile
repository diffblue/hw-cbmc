SRC = smv_language.cpp smv_parser.cpp smv_typecheck.cpp expr2smv.cpp \
      y.tab.cpp lex.yy.cpp smv_parse_tree.cpp

include ../config.inc

INCLUDES= -I $(CBMC)/src

CLEANFILES = smvlang$(LIBEXT) y.tab.h y.tab.cpp lex.yy.cpp y.tab.cpp.output y.output

all: smvlang$(LIBEXT)

###############################################################################

smvlang$(LIBEXT): $(OBJ)
	$(LINKLIB)

y.tab.cpp: parser.y
	$(YACC) $(YFLAGS) $$flags -pyysmv -d parser.y -o y.tab.cpp

y.tab.h: y.tab.cpp
	if [ -e y.tab.hpp ] ; then mv y.tab.hpp y.tab.h ; else \
        mv y.tab.cpp.h y.tab.h ; fi

lex.yy.cpp: scanner.l
	$(LEX) -Pyysmv -olex.yy.cpp scanner.l

# extra dependencies
y.tab$(OBJEXT): y.tab.cpp y.tab.h
lex.yy$(OBJEXT): y.tab.cpp lex.yy.cpp y.tab.h

