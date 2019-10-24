SRC = aiger_language.cpp

include $(CPROVER_DIR)/config.inc
include $(CPROVER_DIR)/common

INCLUDES= -I $(CPROVER_DIR)

CLEANFILES = 

all: aiger$(LIBEXT)

###############################################################################

aiger$(LIBEXT): $(OBJ)
	$(LINKLIB)

