SRC = get_trans.cpp show_modules.cpp unwind.cpp	word_level_trans.cpp \
      property.cpp counterexample_word_level.cpp \
      trans_trace_word_level.cpp instantiate_word_level.cpp

include $(CPROVER_DIR)/config.inc
include $(CPROVER_DIR)/common

INCLUDES= -I $(CPROVER_DIR) -I ..
CXXFLAGS += -D'LOCAL_IREP_IDS=<hw_cbmc_irep_ids.h>'

CLEANFILES = trans-word-level$(LIBEXT)

all: trans-word-level$(LIBEXT)

###############################################################################

trans-word-level$(LIBEXT): $(OBJ)
	$(LINKLIB)

