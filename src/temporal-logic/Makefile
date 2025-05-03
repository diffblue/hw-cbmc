SRC = ctl.cpp \
      ltl.cpp \
      nnf.cpp \
      normalize_property.cpp \
      sva_to_ltl.cpp \
      temporal_logic.cpp \
      trivial_sva.cpp \
      #empty line

include ../config.inc
include ../common

CLEANFILES = temporal-logic$(LIBEXT)

all: temporal-logic$(LIBEXT)

###############################################################################

temporal-logic$(LIBEXT): $(OBJ)
	$(LINKLIB)

