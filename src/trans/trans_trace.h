/*******************************************************************\

Module: Extracting Counterexamples

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_TRANS_COUNTEREXAMPLE_H
#define CPROVER_TRANS_COUNTEREXAMPLE_H

#include <util/hash_cont.h>
#include <util/ui_message.h>
#include <util/threeval.h>
#include <util/namespace.h>
#include <util/decision_procedure.h>

#include <solvers/prop/literal.h>

#include "bmc_map.h"

class trans_tracet
{
public:
  class statet
  {
  public:
    class assignmentt
    {
    public:
      exprt lhs;
      exprt rhs;
      locationt location;
      
      assignmentt():location(static_cast<const locationt &>(get_nil_irep()))
      {
      }
    };

    typedef std::list<assignmentt> assignmentst;
    assignmentst assignments;
  };

  // one state per timeframe
  typedef std::vector<statet> statest;
  statest states;
  
  // mode of whole trace
  std::string mode;
  
  // properties
  struct propertyt
  {
    std::string name;
    tvt status;
    unsigned failing_timeframe;
  };
  
  typedef std::list<propertyt> propertiest;
  propertiest properties;

  // returns the latest failing timeframe  
  unsigned get_max_failing_timeframe() const;

  // returns the earliest failing timeframe  
  unsigned get_min_failing_timeframe() const;
};

// word-level without properties

void compute_trans_trace(
  const decision_proceduret &decision_procedure,
  unsigned no_timeframes,
  const namespacet &ns,
  const irep_idt &module,
  trans_tracet &dest);

// word-level with properties
  
void compute_trans_trace(
  const std::list<bvt> &prop_bv,
  const class prop_convt &solver,
  unsigned no_timeframes,
  const namespacet &ns,
  const irep_idt &module,
  trans_tracet &dest);

// bit-level netlists

void compute_trans_trace(
  const std::list<bvt> &prop_bv,
  const bmc_mapt &bmc_map,
  const class propt &solver,
  const namespacet &ns,
  trans_tracet &dest);

// outputting traces
  
void show_trans_trace(
  const trans_tracet &trace,
  messaget &message,
  const namespacet &ns,
  ui_message_handlert::uit ui);  

void show_trans_trace_vcd(
  const trans_tracet &trace,
  messaget &message,
  const namespacet &ns,
  std::ostream &out);

#endif
