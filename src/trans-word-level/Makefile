SRC = get_trans.cpp show_modules.cpp unwind.cpp	word_level_trans.cpp

include ../config.inc

INCLUDES= -I $(CBMC)/src

CLEANFILES = trans-word-level$(LIBEXT)

all: trans-word-level$(LIBEXT)

###############################################################################

trans-word-level$(LIBEXT): $(OBJ)
	$(LINKLIB)

