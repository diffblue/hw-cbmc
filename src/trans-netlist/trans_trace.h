/*******************************************************************\

Module: Extracting Counterexamples

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_TRANS_TRACE_H
#define CPROVER_TRANS_TRACE_H

#include <util/hash_cont.h>
#include <util/ui_message.h>
#include <util/threeval.h>
#include <util/namespace.h>

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
      source_locationt location;
      
      assignmentt():location(source_locationt::nil())
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

void compute_trans_trace_properties(
  const std::list<std::string> &prop_names,
  const std::list<bvt> &prop_bv,
  const propt &solver,
  unsigned no_timeframes,
  trans_tracet &dest);
  
// outputting traces

void convert(
  const namespacet &,
  const trans_tracet &,
  class xmlt &);
        
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
