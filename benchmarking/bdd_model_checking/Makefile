CPROVER_DIR = ../../lib/cbmc

include $(CPROVER_DIR)/src/config.inc
include $(CPROVER_DIR)/src/common

SRC = benchmark.cpp

INCLUDES = -I ../../src -I $(CPROVER_DIR)/src
CXXFLAGS += -D'LOCAL_IREP_IDS=<hw_cbmc_irep_ids.h>'

OBJ += ../../src/ebmc/bdd_model_checker$(OBJEXT) \
       $(CPROVER_DIR)/src/solvers/solvers$(LIBEXT) \
       $(CPROVER_DIR)/src/util/util$(LIBEXT) \
       $(CPROVER_DIR)/src/big-int/big-int$(LIBEXT)

all: benchmark$(EXEEXT)

benchmark$(EXEEXT): $(OBJ)
	$(LINKBIN)

run: benchmark$(EXEEXT)
	./benchmark$(EXEEXT)

clean:
	$(RM) benchmark$(EXEEXT) *.o *.d
