/*******************************************************************\

Module: Transition Systems for EBMC

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "build_transition_system.h"

#include <util/cmdline.h>
#include <util/message.h>

#include <smvlang/smv_ebmc_language.h>
#include <verilog/verilog_ebmc_language.h>

#include "ebmc_error.h"
#include "transition_system.h"

#include <fstream>
#include <set>

static std::set<std::string> file_extensions(const cmdlinet::argst &args)
{
  std::set<std::string> result;

  for(auto &arg : args)
  {
    std::size_t ext_pos = arg.rfind('.');

    if(ext_pos != std::string::npos)
    {
      auto ext = std::string(arg, ext_pos + 1, std::string::npos);
      result.insert(ext);
    }
  }

  return result;
}

std::optional<transition_systemt> ebmc_languagest::transition_system()
{
  auto extensions = file_extensions(cmdline.args);
  auto ext_used = [&extensions](const char *ext)
  { return extensions.find(ext) != extensions.end(); };

  bool have_smv = ext_used("smv");
  bool have_verilog = ext_used("v") || ext_used("sv");

  if(have_smv && have_verilog)
  {
    throw ebmc_errort{} << "no support for mixed-language models";
  }

  if(have_smv)
  {
    return smv_ebmc_languaget{cmdline, message_handler}.transition_system();
  }
  else if(have_verilog)
  {
    return verilog_ebmc_languaget{cmdline, message_handler}.transition_system();
  }
  else
  {
    throw ebmc_errort{} << "no support for given input file extensions";
  }
}
