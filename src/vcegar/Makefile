SRC = vcegar.cpp parseoptions.cpp discover_predicates.cpp \
      canonicalize.cpp partitioning.cpp instantiate_guards.cpp \
      abstractor.cpp  main.cpp vcegar_loop.cpp bmc.cpp \
      predicates.cpp refiner.cpp  simulator.cpp \
      modelchecker_smv.cpp predabs_aux.cpp \
      abstract_expression.cpp vcegar_util.cpp network_info.cpp \
      abstract_counterexample.cpp

OBJ = $(SRC:.cpp=$(OBJEXT)) \
      ../util/util$(LIBEXT) \
      ../langapi/langapi$(LIBEXT) \
      ../smvlang/smvlang$(LIBEXT) \
      ../verilog/verilog$(LIBEXT) \
      ../solvers/solvers$(LIBEXT) \
      ../satqe/satqe$(LIBEXT) \
      ../big-int/bigint$(OBJEXT) \
      ../ebmc/ebmc_base$(LIBEXT) \
      ../trans/trans$(LIBEXT)

INCLUDES= -I ../$(CHAFF)  -I ../util

LIBS =

include ../config.inc
include ../common

all: vcegar$(EXEEXT)

GCCFLAGS += -Wall -g  

###############################################################################

vcegar$(EXEEXT): $(OBJ)
	$(CXX) $(LINKFLAGS) -o $@ $(OBJ) $(LIBS) 

clean:
	rm -f $(SRC:.cpp=$(OBJEXT)) vcegar$(EXEEXT)

