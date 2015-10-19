SRC = get_trans.cpp show_modules.cpp unwind.cpp	word_level_trans.cpp

include ../config.inc

INCLUDES= -I $(CBMC)/src

CLEANFILES = trans$(LIBEXT)

all: trans$(LIBEXT)

###############################################################################

trans$(LIBEXT): $(OBJ)
	$(LINKLIB)

