SRC = ctl.cpp \
      hoa.cpp \
      ltl.cpp \
      ltl_to_buechi.cpp \
      ltl_sva_to_string.cpp \
      nnf.cpp \
      normalize_property.cpp \
      rewrite_sva_sequence.cpp \
      sva_sequence_match.cpp \
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

