SRC = aiger_language.cpp

include ../config.inc

INCLUDES= -I $(CBMC)/src

CLEANFILES = 

all: aiger$(LIBEXT)

###############################################################################

aiger$(LIBEXT): $(OBJ)
	$(LINKLIB)

