SRC = counterexample_word_level.cpp \
      get_trans.cpp \
      lasso.cpp \
      obligations.cpp \
      property.cpp \
      trans_trace_word_level.cpp \
      instantiate_word_level.cpp \
      sequence.cpp \
      show_module_hierarchy.cpp \
      unwind.cpp \
      word_level_trans.cpp

include ../config.inc
include ../common

CLEANFILES = trans-word-level$(LIBEXT)

all: trans-word-level$(LIBEXT)

###############################################################################

trans-word-level$(LIBEXT): $(OBJ)
	$(LINKLIB)

