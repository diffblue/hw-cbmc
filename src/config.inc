CBMC = ../../lib/cbmc

CXXFLAGS += -Wno-unused-variable -Wno-error=unused-but-set-variable

include $(CBMC)/src/config.inc
include $(CBMC)/src/common

