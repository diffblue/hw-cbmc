SRC = \
      vl_simulator.cpp \
      vlsim_main.cpp \
      vlsim_parse_options.cpp \
      vlsim_version.cpp \
      #empty line

OBJ+= $(CPROVER_DIR)/util/util$(LIBEXT) \
      $(CPROVER_DIR)/langapi/langapi$(LIBEXT) \
      $(CPROVER_DIR)/big-int/big-int$(LIBEXT) \
      ../ebmc/ebmc_language$(OBJEXT) \
      ../ebmc/show_modules$(OBJEXT) \
      ../ebmc/transition_system$(OBJEXT) \
      ../temporal-logic/temporal-logic$(LIBEXT) \
      ../trans-word-level/trans-word-level$(LIBEXT) \
      ../verilog/verilog$(LIBEXT)

include ../config.inc
include ../common

# get version from git
GIT_INFO = $(shell git describe --tags --always --dirty || echo "n/a")
RELEASE_INFO = const char *VLSIM_VERSION="$(VLSIM_VERSION) ($(GIT_INFO))";
GIT_INFO_FILE = vlsim_version.cpp

$(GIT_INFO_FILE):
	echo '$(RELEASE_INFO)' > $@

KNOWN_RELEASE_INFO = $(shell cat $(GIT_INFO_FILE) 2>/dev/null)
ifneq ($(RELEASE_INFO), $(KNOWN_RELEASE_INFO))
.PHONY: $(GIT_INFO_FILE)
endif

CLEANFILES = $(GIT_INFO_FILE) vlsim$(EXEEXT)

all: vlsim$(EXEEXT)

ifdef DEBUG
CXXFLAGS += -DDEBUG
endif

###############################################################################

vlsim$(EXEEXT): $(OBJ)
	$(LINKBIN)
