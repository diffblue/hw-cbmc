/*******************************************************************\

Module: FastPPA Estimation Parse Options

Author: Kiro

\*******************************************************************/

#ifndef CPROVER_FASTPPA_FASTPPA_PARSE_OPTIONS_H
#define CPROVER_FASTPPA_FASTPPA_PARSE_OPTIONS_H

#include <util/parse_options.h>
#include <util/ui_message.h>

#define FASTPPA_OPTIONS                                                        \
  "(process):"                                                                 \
  "(clock-freq):"                                                              \
  "(toggle-rate):"                                                             \
  "(netlist)"                                                                  \
  "(top):"                                                                     \
  "(verbosity):"                                                               \
  "(version)"                                                                  \
  "I:D:(systemverilog)"

class fastppa_parse_optionst : public parse_options_baset
{
public:
  int doit() override;
  void help() override;

  fastppa_parse_optionst(int argc, const char **argv)
    : parse_options_baset(FASTPPA_OPTIONS, argc, argv, "fastppa"),
      ui_message_handler(cmdline, "fastppa")
  {
  }

protected:
  void register_languages() override;

  ui_message_handlert ui_message_handler;
};

#endif // CPROVER_FASTPPA_FASTPPA_PARSE_OPTIONS_H
