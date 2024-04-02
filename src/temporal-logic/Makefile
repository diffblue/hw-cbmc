SRC = negate_property.cpp \
      normalize_property.cpp \
      temporal_logic.cpp \
      #empty line

include ../config.inc
include ../common

CLEANFILES = temporal-logic$(LIBEXT)

all: temporal-logic$(LIBEXT)

###############################################################################

temporal-logic$(LIBEXT): $(OBJ)
	$(LINKLIB)

