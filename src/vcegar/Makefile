SRC = vcegar.cpp parseoptions.cpp discover_predicates.cpp \
      canonicalize.cpp partitioning.cpp instantiate_guards.cpp \
      abstractor.cpp main.cpp vcegar_loop.cpp bmc.cpp \
      predicates.cpp refiner.cpp simulator.cpp \
      modelchecker_smv.cpp predabs_aux.cpp \
      abstract_expression.cpp vcegar_util.cpp network_info.cpp \
      abstract_counterexample.cpp

OBJ = $(SRC:.cpp=$(OBJEXT)) \
      $(CBMC)/src/util/util$(LIBEXT) \
      $(CBMC)/src/langapi/langapi$(LIBEXT) \
      $(CBMC)/src/solvers/solvers$(LIBEXT) \
      $(CBMC)/src/big-int/bigint$(OBJEXT) \
      ../smvlang/smvlang$(LIBEXT) \
      ../verilog/verilog$(LIBEXT) \
      ../satqe/satqe$(LIBEXT) \
      ../ebmc/ebmc_base$(OBJEXT) \
      ../trans/trans$(LIBEXT)

include ../config.inc
include ../common

LIBS =

all: vcegar$(EXEEXT)

GCCFLAGS += -Wall -g  

###############################################################################

vcegar$(EXEEXT): $(OBJ)
	$(LINKBIN)

