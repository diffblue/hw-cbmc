SRC = get_trans.cpp \
      show_modules.cpp \
      show_module_hierarchy.cpp \
      unwind.cpp \
      word_level_trans.cpp \
      property.cpp \
      counterexample_word_level.cpp \
      trans_trace_word_level.cpp \
      instantiate_word_level.cpp

include ../config.inc
include ../common

CLEANFILES = trans-word-level$(LIBEXT)

all: trans-word-level$(LIBEXT)

###############################################################################

trans-word-level$(LIBEXT): $(OBJ)
	$(LINKLIB)

