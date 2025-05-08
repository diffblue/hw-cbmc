SRC = smv_expr.cpp \
      smv_language.cpp \
      smv_parser.cpp \
      smv_typecheck.cpp \
      expr2smv.cpp \
      smv_y.tab.cpp \
      lex.yy.cpp \
      smv_parse_tree.cpp \
      smv_range.cpp

include ../config.inc
include ../common

CLEANFILES = smvlang$(LIBEXT) smv_y.tab.h smv_y.tab.cpp lex.yy.cpp smv_y.output

all: smvlang$(LIBEXT)

###############################################################################

smvlang$(LIBEXT): $(OBJ)
	$(LINKLIB)

smv_y.tab.cpp: parser.y
	$(YACC) $(YFLAGS) $$flags -pyysmv --defines=smv_y.tab.h -d parser.y -o $@

smv_y.tab.h: smv_y.tab.cpp

lex.yy.cpp: scanner.l
	$(LEX) -Pyysmv -olex.yy.cpp scanner.l

# extra dependencies
smv_y.tab$(OBJEXT): smv_y.tab.cpp smv_y.tab.h
lex.yy$(OBJEXT): smv_y.tab.cpp lex.yy.cpp smv_y.tab.h

