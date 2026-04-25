SRC = aiger_language.cpp \
      #empty line

ifneq ($(BUILD_ENV),MSVC)
SRC += aiger_ebmc_language.cpp
AIGER_C_OBJ = aiger_c$(OBJEXT)
endif

include ../config.inc
include ../common

CLEANFILES = aiger$(LIBEXT) $(AIGER_C_OBJ)

all: aiger$(LIBEXT)

###############################################################################

aiger_c$(OBJEXT): ../ic3/aiger/aiger.c
	$(CC) -c -o $@ $<

aiger$(LIBEXT): $(OBJ) $(AIGER_C_OBJ)
	$(LINKLIB)
