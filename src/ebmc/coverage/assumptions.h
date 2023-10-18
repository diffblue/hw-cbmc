#ifndef SOLVER_COVERAGE_ASSUMPTIONS
#define SOLVER_COVERAGE_ASSUMPTIONS

#include <solvers/prop/literal.h>
#include <trans-netlist/bmc_map.h>

#include <map>
#include <vector>

enum coverage_resultt {COVERED, NOTCOVERED, UNKNOWN};

enum coverage_methodt {CORE,  INDUCTION, INDUCTION_SKIP, INDUCTION_SCRATCH_SKIP, INDUCTION_SCRATCH, INTERPOLATION, INTERPOLATION_SKIP, NONE, CE, CE_SKIP};
enum force_typet {ZERO, ONE, NONDET};

class core_testt
{
public:
  unsigned not_covered;
  fine_timet total_time;
  core_testt(){
    
    not_covered = 0;
  }
  void print();
  
};

class ce_testt
{
public:
  unsigned counterexample;
  unsigned reused_counterexample;
  
  fine_timet total_time;
  
  ce_testt();
  void print();  
};

class induction_testt
{
public:
  unsigned total_tests;
  unsigned inductive;
  unsigned nondet_inductive;
  unsigned non_inductive;
  fine_timet total_time;
  
  induction_testt();
  void print();  
};

class naive_testt
{
public:
  unsigned total_tests;
  unsigned fixedpoint;
  unsigned nondet_fixedpoint;
  fine_timet total_time;
  unsigned counterexample;
  unsigned reused_counterexample;  
  naive_testt();
  void print();  
};


class interpolation_testt
{
public:
  unsigned total_tests;
  unsigned fixedpoint;
  unsigned nondet_fixedpoint;
  unsigned counterexample;
  unsigned reused_counterexample;
  fine_timet total_time;
  interpolation_testt();
  void print();
};


class force_valuet
{
public:
  
  unsigned force_val_var;
  force_typet force_val;
  force_valuet(unsigned u, force_typet f) {
    force_val_var = u;
    force_val = f;
  }
  
};

class force_multiplexert
{
public:
  
  unsigned force_select_var;
  unsigned force_val_var;
  class resultt
  {
  public:
    coverage_resultt result;
    coverage_methodt method;
    std::string get_method()
    {
      std::string ret_method = 
        method == CORE ? "CORE" :
        method == CE ? "CE" :
        method == CE_SKIP ? "CE_SKIP" :
        method == INDUCTION ? "INDUCTION" :
        method == INDUCTION_SKIP ? "INDUCTION_SKIP" :
        method == INDUCTION_SCRATCH ? "INDUCTION_SCRATCH" : 
        method == INDUCTION_SCRATCH_SKIP ? "INDUCTION_SCRATCH_SKIP" : 
        method == INTERPOLATION ? "INTERPOLATION" : 
        method == INTERPOLATION_SKIP ? "INTERPOLATION_SKIP" : "NONE"; 
      return ret_method;
    }

  };
  
  
  std::vector<resultt> coverage; //could be made a vector to store results of various timeframes
  force_multiplexert() {
    resultt r;
    r.result = UNKNOWN;
    r.method = NONE;
    coverage.resize(3, r); // order ZERO, ONE, NONDET
  }
  
  force_multiplexert(unsigned fsv, unsigned fvv) {
    force_select_var = fsv;
    force_val_var = fvv;

    resultt r;
    r.result = UNKNOWN;
    r.method = NONE;

    coverage.resize(3, r); // order ZERO, ONE, NONDET
  }

  void set_coverage(unsigned id, coverage_resultt r, coverage_methodt m)
  {
    assert(id < coverage.size());
    coverage.at(id).result = r;
    coverage.at(id).method = m;
  }

  
};

class assumptionst
{

public:
  std::map<std::string, force_multiplexert> &force_selects_node;
//  std::map<std::string, unsigned> &force_vals_node;

  std::map<std::string, force_multiplexert> &force_selects_latch;
//  std::map<std::string, unsigned> &force_vals_latch;

  std::map<unsigned, force_valuet > force_map;
  
public:
  
  void get_assumptions(std::vector<literalt> &assumptions,
                       const bmc_mapt &nbm,
                       bool force,
                       unsigned bound);

  void get_assumptions_for_timeframe(std::vector<literalt> &assumptions,
                                     const bmc_mapt &nbm,
                                     bool force,
                                     unsigned c);
  
  void insert_assumption(const std::pair<std::string, force_multiplexert> &iter,
                         std::vector<literalt> &assumptions,
                         const bmc_mapt &nbm,
                         bool force,
                         unsigned bound);

  void insert_assumption_for_timeframe(const std::map<std::string, force_multiplexert> &given_map,
                                       std::vector<literalt> &assumptions,
                                       const bmc_mapt &nbm,
                                       unsigned c,
                                       bool force);
  assumptionst(std::map<std::string, force_multiplexert> &force_selects_node1,
               std::map<std::string, force_multiplexert> &force_selects_latch1):
  force_selects_node(force_selects_node1),
    force_selects_latch(force_selects_latch1)
    {
      force_map.insert(std::make_pair(0, force_valuet(0, NONDET))); //dirty
    }
};

extern core_testt core_test;
extern induction_testt induction_test;
extern induction_testt induction_test_from_scratch;
extern interpolation_testt interpolation_test;
extern ce_testt ce_test;
extern naive_testt naive_test;
extern std::ofstream log;
extern std::ofstream log_naive;

#endif
