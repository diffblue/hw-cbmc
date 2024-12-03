SRC = \
      verilog_indexer.cpp \
      vlindex_main.cpp \
      vlindex_parse_options.cpp \
      vlindex_parser.cpp \
      #empty line

OBJ+= $(CPROVER_DIR)/util/util$(LIBEXT) \
      $(CPROVER_DIR)/langapi/langapi$(LIBEXT) \
      $(CPROVER_DIR)/big-int/big-int$(LIBEXT) \
      ../verilog/verilog$(LIBEXT)

include ../config.inc
include ../common

CLEANFILES = vlindex$(EXEEXT)

all: vlindex$(EXEEXT)

ifdef DEBUG
CXXFLAGS += -DDEBUG
endif

###############################################################################

vlindex$(EXEEXT): $(OBJ)
	$(LINKBIN)
