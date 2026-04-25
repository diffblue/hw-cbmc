/*******************************************************************\

Module: Transition Systems for EBMC

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "build_transition_system.h"

#include <util/cmdline.h>
#include <util/message.h>

#ifndef _MSC_VER
#  include <aiger/aiger_ebmc_language.h>
#endif
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

#ifndef _MSC_VER
  bool have_aiger = ext_used("aig") || ext_used("aag");
#else
  bool have_aiger = false;
#endif

  if((have_smv ? 1 : 0) + (have_verilog ? 1 : 0) + (have_aiger ? 1 : 0) > 1)
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
  else if(have_aiger)
  {
#ifndef _MSC_VER
    return aiger_ebmc_languaget{cmdline, message_handler}.transition_system();
#endif
  }
  else
  {
    throw ebmc_errort{} << "no support for given input file extensions";
  }
}
