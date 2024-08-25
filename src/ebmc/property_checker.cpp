/*******************************************************************\

Module: EBMC Property Checker

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "property_checker.h"

#include <util/string2int.h>

#include "bmc.h"
#include "ebmc_error.h"
#include "ebmc_solver_factory.h"
#include "report_results.h"

int word_level_bmc(
  const cmdlinet &cmdline,
  const transition_systemt &transition_system,
  ebmc_propertiest &properties,
  message_handlert &message_handler)
{
  auto solver_factory = ebmc_solver_factory(cmdline);

  bool convert_only = cmdline.isset("smt2") || cmdline.isset("outfile") ||
                      cmdline.isset("show-formula");

  int result = 0;

  try
  {
    if(cmdline.isset("max-bound"))
    {
      if(convert_only)
        throw ebmc_errort() << "please set a specific bound";

      const std::size_t max_bound =
        unsafe_string2size_t(cmdline.get_value("max-bound"));

      for(std::size_t bound = 1; bound <= max_bound; bound++)
      {
        messaget message{message_handler};
        message.status() << "Doing BMC with bound " << bound << messaget::eom;

#if 0
        const namespacet ns(transition_system.symbol_table);
        CHECK_RETURN(trans_expr.has_value());
        ::unwind(*trans_expr, *message_handler, solver, bound+1, ns, true);
        result=finish_word_level_bmc(solver);
#endif
      }

      const namespacet ns(transition_system.symbol_table);
      report_results(cmdline, properties, ns, message_handler);
    }
    else
    {
      std::size_t bound;

      if(cmdline.isset("bound"))
      {
        bound = unsafe_string2unsigned(cmdline.get_value("bound"));
      }
      else
      {
        messaget message{message_handler};
        message.warning() << "using default bound 1" << messaget::eom;
        bound = 1;
      }

      if(!convert_only)
        if(properties.properties.empty())
          throw "no properties";

      bmc(
        bound,
        convert_only,
        transition_system,
        properties,
        solver_factory,
        message_handler);

      if(!convert_only)
      {
        const namespacet ns(transition_system.symbol_table);
        report_results(cmdline, properties, ns, message_handler);
        result = properties.exit_code();
      }
    }
  }

  catch(const char *e)
  {
    messaget message{message_handler};
    message.error() << e << messaget::eom;
    return 10;
  }

  catch(const std::string &e)
  {
    messaget message{message_handler};
    message.error() << e << messaget::eom;
    return 10;
  }

  catch(int)
  {
    return 10;
  }

  return result;
}

int property_checker(
  const cmdlinet &cmdline,
  const transition_systemt &transition_system,
  ebmc_propertiest &properties,
  message_handlert &message_handler)
{
  // default engine is word-level BMC
  return word_level_bmc(
    cmdline, transition_system, properties, message_handler);
}
