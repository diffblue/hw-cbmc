SRC = cube_set.cpp cubes.cpp satqe_satcheck.cpp

LIBS =

include ../config.inc
include ../common

all: satqe$(LIBEXT)

ifneq ($(MINISAT),)
MINISAT_INCLUDE=-I ../$(MINISAT)
endif

INCLUDES+= $(MINISAT_INCLUDE)

###############################################################################

satqe$(LIBEXT): $(OBJ)
	$(LINKLIB)

