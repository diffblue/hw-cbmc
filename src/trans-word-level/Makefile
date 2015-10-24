SRC = get_trans.cpp show_modules.cpp unwind.cpp	word_level_trans.cpp \
      property_word_level.cpp counterexample_word_level.cpp \
      trans_trace_word_level.cpp instantiate_word_level.cpp

include ../config.inc

INCLUDES= -I $(CBMC)/src

CLEANFILES = trans-word-level$(LIBEXT)

all: trans-word-level$(LIBEXT)

###############################################################################

trans-word-level$(LIBEXT): $(OBJ)
	$(LINKLIB)

