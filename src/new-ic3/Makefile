SRC = new_ic3_engine.cpp \
      #empty line

include ../config.inc
include ../common

CXXFLAGS += -I ../ic3/minisat

all: new-ic3$(LIBEXT)

clean:
	$(RM) *.o *.d new-ic3$(LIBEXT)

new-ic3$(LIBEXT): $(OBJ)
	$(LINKLIB)
