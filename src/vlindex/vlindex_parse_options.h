/*******************************************************************\

Module: Command Line Parsing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef VLINDEX_PARSEOPTIONS_H
#define VLINDEX_PARSEOPTIONS_H

#include <util/parse_options.h>
#include <util/ui_message.h>

#include <ebmc/ebmc_version.h>

class vlindex_parse_optionst : public parse_options_baset
{
public:
  int doit() override;
  void help() override;

  vlindex_parse_optionst(int argc, const char **argv)
    : parse_options_baset(
        "(version)"
        "(top)"
        "(hierarchy)"
        "(modules)"
        "(packages)(classes)(interfaces)(udps)(instances)(tasks)(functions)"
        "(sequences)(properties)"
        "(symlinks)(files)"
        "(1800-2017)(1800-2012)(1800-2009)(1800-2005)"
        "(1364-2005)(1364-2001)(1364-2001-noconfig)(1364-1995)"
        "I:(preprocess)",
        argc,
        argv,
        std::string("EBMC ") + EBMC_VERSION),
      ui_message_handler(cmdline, std::string("EBMC ") + EBMC_VERSION)
  {
  }

  virtual ~vlindex_parse_optionst() = default;

protected:
  ui_message_handlert ui_message_handler;
};

#endif
