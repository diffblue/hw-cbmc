/*******************************************************************\

Module: Command File (-f) Support

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Expand command files (.f files) into command-line arguments

#include "command_file.h"

#include <util/cmdline.h>
#include <util/prefix.h>

#include "ebmc_error.h"

#include <cstdlib>
#include <filesystem>
#include <fstream>
#include <string>
#include <string_view>
#include <vector>

/// Extract the argument to a single-letter option like -I or -D.
/// The argument can be concatenated (-Ipath) or separated by whitespace
/// (-I path) on the same line.
static std::string option_argument(const std::string &token, std::size_t pos)
{
  if(pos < token.size())
  {
    auto arg_begin = token.find_first_not_of(" \t", pos);
    if(arg_begin != std::string::npos)
      return token.substr(arg_begin);
  }
  return {};
}

/// Expand environment variables of the form $VAR or ${VAR} in a string.
/// Unknown variables are replaced by an empty string.
std::string expand_environment_variables(std::string_view s)
{
  std::string result;
  result.reserve(s.size());

  for(std::size_t i = 0; i < s.size(); ++i)
  {
    if(s[i] == '$' && i + 1 < s.size())
    {
      std::string var_name;

      if(s[i + 1] == '{')
      {
        // ${VAR} form
        auto close = s.find('}', i + 2);
        if(close == std::string_view::npos)
        {
          // no closing brace, treat literally
          result += s[i];
          continue;
        }
        var_name = s.substr(i + 2, close - (i + 2));
        i = close;
      }
      else
      {
        // $VAR form: variable name is [A-Za-z0-9_]+
        std::size_t start = i + 1;
        std::size_t end = start;
        while(
          end < s.size() &&
          (std::isalnum(static_cast<unsigned char>(s[end])) || s[end] == '_'))
        {
          ++end;
        }
        if(end == start)
        {
          // lone $ not followed by valid name char, treat literally
          result += s[i];
          continue;
        }
        var_name = s.substr(start, end - start);
        i = end - 1;
      }

      const char *value = std::getenv(var_name.c_str());
      if(value != nullptr)
        result += value;
    }
    else
    {
      result += s[i];
    }
  }

  return result;
}

static void expand_command_file(
  const std::filesystem::path &path,
  cmdlinet &cmdline,
  std::size_t depth)
{
  if(depth > 20)
    throw ebmc_errort() << "recursive -f nesting exceeds limit";

  std::ifstream file(path);
  if(!file)
    throw ebmc_errort() << "failed to open command file " << path.string();

  // file names in the command file are relative to the
  // directory of the command file
  auto base_dir = path.parent_path();

  std::string line;
  while(std::getline(file, line))
  {
    // skip empty lines and comments
    if(line.empty() || has_prefix(line, "//"))
      continue;

    // strip leading and trailing whitespace
    auto begin = line.find_first_not_of(" \t\r");
    if(begin == std::string::npos)
      continue;
    auto end = line.find_last_not_of(" \t\r");
    auto token = line.substr(begin, end - begin + 1);

    if(token.empty())
      continue;

    // expand environment variables ($VAR and ${VAR})
    token = expand_environment_variables(token);

    if(has_prefix(token, "--"))
    {
      // long option (--name) possibly with a value on the same line
      std::string option_name;
      std::string option_value;

      auto space_pos = token.find_first_of(" \t", 2);
      if(space_pos != std::string::npos)
      {
        option_name = token.substr(2, space_pos - 2);
        auto val_begin = token.find_first_not_of(" \t", space_pos);
        if(val_begin != std::string::npos)
          option_value = token.substr(val_begin);
      }
      else
        option_name = token.substr(2);

      if(!cmdline.has_option(option_name))
      {
        throw ebmc_errort()
          << "unknown option " << token << " in command file " << path.string();
      }

      if(option_value.empty())
        cmdline.set(option_name);
      else
        cmdline.set(option_name, option_value);
    }
    else if(has_prefix(token, "-f"))
    {
      auto arg = option_argument(token, 2);

      if(arg.empty())
      {
        // argument on the next non-blank, non-comment line
        std::string arg_line;
        while(std::getline(file, arg_line))
        {
          auto arg_begin = arg_line.find_first_not_of(" \t\r");
          if(arg_begin == std::string::npos)
            continue;
          auto arg_end = arg_line.find_last_not_of(" \t\r");
          arg = arg_line.substr(arg_begin, arg_end - arg_begin + 1);
          if(arg.empty() || has_prefix(arg, "//"))
          {
            arg.clear();
            continue;
          }
          break;
        }
      }

      if(arg.empty())
        throw ebmc_errort() << "-f in command file without argument";

      auto nested_path = std::filesystem::path(arg);
      if(nested_path.is_relative() && !base_dir.empty())
        nested_path = base_dir / nested_path;
      expand_command_file(nested_path, cmdline, depth + 1);
    }
    else if(has_prefix(token, "-I"))
    {
      auto arg = option_argument(token, 2);
      if(arg.empty())
        throw ebmc_errort() << "-I in command file without argument";
      auto inc_path = std::filesystem::path(arg);
      if(inc_path.is_relative() && !base_dir.empty())
        inc_path = base_dir / inc_path;
      cmdline.set('I', inc_path.string());
    }
    else if(has_prefix(token, "-D"))
    {
      auto arg = option_argument(token, 2);
      if(arg.empty())
        throw ebmc_errort() << "-D in command file without argument";
      cmdline.set('D', arg);
    }
    else if(token[0] == '-')
    {
      // single-dash long option (-name), as used by EDA tools
      std::string option_name;
      std::string option_value;

      auto space_pos = token.find_first_of(" \t", 1);
      if(space_pos != std::string::npos)
      {
        option_name = token.substr(1, space_pos - 1);
        auto val_begin = token.find_first_not_of(" \t", space_pos);
        if(val_begin != std::string::npos)
          option_value = token.substr(val_begin);
      }
      else
        option_name = token.substr(1);

      if(!cmdline.has_option(option_name))
      {
        throw ebmc_errort()
          << "unknown option " << token << " in command file " << path.string();
      }

      if(option_value.empty())
        cmdline.set(option_name);
      else
        cmdline.set(option_name, option_value);
    }
    else if(token[0] != '+')
    {
      auto file_path = std::filesystem::path(token);
      if(file_path.is_relative() && !base_dir.empty())
        file_path = base_dir / file_path;
      cmdline.args.push_back(file_path.string());
    }
    else
    {
      throw ebmc_errort() << "unknown option " << token << " in command file "
                          << path.string();
    }
  }
}

void expand_command_files(cmdlinet &cmdline)
{
  auto &values = cmdline.get_values('f');

  if(values.empty())
    return;

  // Copy the values since we'll be modifying cmdline
  std::vector<std::string> command_files(values.begin(), values.end());

  for(auto &command_file_name : command_files)
  {
    expand_command_file(std::filesystem::path(command_file_name), cmdline, 0);
  }
}
