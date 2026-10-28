SRC = ic3_solver.cpp \
      ic3_engine.cpp \
      #empty line

include ../config.inc
include ../common

CXXFLAGS += -I ../old-ic3/minisat

all: ic3$(LIBEXT)

clean:
	$(RM) *.o *.d ic3$(LIBEXT)

ic3$(LIBEXT): $(OBJ)
	$(LINKLIB)
