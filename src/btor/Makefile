SRC = btor_language.cpp \
      btor_parser.cpp \
      btor_ebmc_language.cpp \
      #empty line

include ../config.inc
include ../common

CLEANFILES = btor$(LIBEXT)

all: btor$(LIBEXT)

###############################################################################

btor$(LIBEXT): $(OBJ)
	$(LINKLIB)
