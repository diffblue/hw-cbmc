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
    
    bool property_failed;
    
    statet():property_failed(false)
    {
    }
  };

  // one state per timeframe
  typedef std::vector<statet> statest;
  statest states;
  
  // mode of whole trace
  std::string mode;
  
  // returns the latest failing timeframe  
  unsigned get_max_failing_timeframe() const;

  // returns the earliest failing timeframe  
  unsigned get_min_failing_timeframe() const;
};

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
