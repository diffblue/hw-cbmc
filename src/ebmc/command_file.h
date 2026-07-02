/*******************************************************************\

Module: Command File (-f) Support

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Expand command files (.f files) into command-line arguments

#ifndef CPROVER_EBMC_COMMAND_FILE_H
#define CPROVER_EBMC_COMMAND_FILE_H

#include <string>
#include <string_view>

class cmdlinet;

/// Read -f command files and expand their contents into cmdline.args.
/// Each line of a command file is treated as a file name or option.
/// Blank lines and lines starting with // are ignored.
void expand_command_files(cmdlinet &);

/// Expand environment variables of the form $VAR or ${VAR} in a string.
/// Unknown variables are replaced by an empty string.
std::string expand_environment_variables(std::string_view);

#endif // CPROVER_EBMC_COMMAND_FILE_H
