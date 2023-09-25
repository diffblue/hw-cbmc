/*******************************************************************\

Module: Verilog Preprocessing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "verilog_preprocessor.h"

#include <util/config.h>
#include <util/file_util.h>
#include <util/unicode.h>

#include "verilog_preprocessor_error.h"

#include <fstream>

/*******************************************************************\

Function: verilog_preprocessort::contextt::make_source_location

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

source_locationt verilog_preprocessort::contextt::make_source_location() const
{
  source_locationt result;

  result.set_file(filename);
  result.set_line(tokenizer->line_no());

  return result;
}

/*******************************************************************\

Function: verilog_preprocessort::as_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string verilog_preprocessort::as_string(const std::vector<tokent> &tokens)
{
  std::string result;

  for(auto &t : tokens)
    result.append(t.text);

  return result;
}

/*******************************************************************\

Function: verilog_preprocessort::vector_token_sourcet::get_token_from_stream

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_preprocessort::vector_token_sourcet::get_token_from_stream()
{
  if(pos == tokens.end())
  {
    token.text.clear();
    token.kind = tokent::END_OF_FILE;
  }
  else
  {
    token = *pos;
    pos++;
  }
}

/*******************************************************************\

Function: verilog_preprocessort::include

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_preprocessort::include(const std::string &filename)
{
  // first try filename as is
  {
#ifdef _MSC_VER
    auto in = new std::ifstream(widen(filename));
#else
    auto in = new std::ifstream(filename);
#endif

    if(*in)
    {
      context_stack.emplace_back(true, in, filename);
      context().print_line_directive(out, 1); // 'enter'
      return; // done
    }
    else
      delete in;
  }

  // try include paths in given order
  for(const auto &path : config.verilog.include_paths)
  {
    auto full_name = concat_dir_file(path, filename);

#ifdef _MSC_VER
    auto in = new std::ifstream(widen(full_name));
#else
    auto in = new std::ifstream(full_name);
#endif

    if(*in)
    {
      context_stack.emplace_back(true, in, filename);
      context().print_line_directive(out, 1); // 'enter'
      return; // done
    }

    delete in;
  }

  throw verilog_preprocessor_errort()
    << "include file `" << filename << "' not found";
}

/*******************************************************************\

Function: verilog_preprocessort::preprocessor

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_preprocessort::preprocessor()
{
  try
  {
    // the first context is the input file
    context_stack.emplace_back(false, &in, filename);

    context().print_line_directive(out, 0); // 'neither'

    while(!context_stack.empty())
    {
      while(!tokenizer().eof())
      {
        auto token = tokenizer().next_token();
        if(token == '`')
          directive();
        else if(condition)
        {
          auto a_it = context().define_arguments.find(token.text);
          if(a_it == context().define_arguments.end())
            out << token;
          else
          {
            // Create a new context for the define argument.
            // We then continue in that context.
            context_stack.emplace_back(a_it->second);
          }
        }
      }

      const bool is_file = context().is_file();
      context_stack.pop_back();

      // print the line directive when we exit an include file
      if(!context_stack.empty() && is_file)
        context().print_line_directive(out, 2); // 'exit'
    }
  }
  catch(const verilog_preprocessor_errort &e)
  {
    if(!context_stack.empty())
      error().source_location = context().make_source_location();
    error() << e.what() << eom;
    throw 0;
  }
}

/*******************************************************************\

Function: verilog_preprocessort::parse_define_parameters

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

auto verilog_preprocessort::parse_define_parameters() -> definet::parameterst
{
  tokenizer().next_token(); // eat (

  definet::parameterst result;

  while(true)
  {
    tokenizer().skip_ws();

    auto parameter = tokenizer().next_token();
    if(!parameter.is_identifier())
      throw verilog_preprocessor_errort() << "expecting a define parameter";

    result.push_back(parameter.text);

    tokenizer().skip_ws();

    auto token = tokenizer().next_token();

    if(token == ')')
      break; // done
    else if(token == ',')
      continue;           // keep going
    else if(token == '=') // SystemVerilog 2009
      throw verilog_preprocessor_errort()
        << "default parameters are not supported yet";
    else
      throw verilog_preprocessor_errort() << "expecting a define parameter";
  }

  return result;
}

/*******************************************************************\

Function: verilog_preprocessort::parse_define_arguments

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

auto verilog_preprocessort::parse_define_arguments(const definet &define)
  -> std::map<std::string, std::vector<tokent>>
{
  if(define.parameters.empty())
    return {};

  if(tokenizer().next_token() != '(')
    throw verilog_preprocessor_errort() << "expecting define arguments";

  // We start with a vector of size 1,
  // which contains one empty vector of argument tokens.
  std::vector<std::vector<tokent>> arguments = {{}};

  while(true)
  {
    if(tokenizer().eof())
      throw verilog_preprocessor_errort()
        << "eof inside a define argument list";

    auto token = tokenizer().next_token();
    if(token == ',')
    {
      arguments.push_back({}); // next argument
      tokenizer().skip_ws();
    }
    else if(token == ')')
      break; // done
    else
      arguments.back().push_back(std::move(token));
  }

  // does the number of arguments match the number of parameters?
  if(arguments.size() != define.parameters.size())
    throw verilog_preprocessor_errort()
      << "expected " << define.parameters.size() << " arguments, but got "
      << arguments.size();

  // sort into the map
  std::map<std::string, std::vector<tokent>> result;

  for(std::size_t i = 0; i < define.parameters.size(); i++)
    result[define.parameters[i]] = std::move(arguments[i]);

  return result;
}

/*******************************************************************\

Function: verilog_preprocessort::directive

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_preprocessort::directive()
{
  // we expect an identifier after the backtick
  const auto directive_token = tokenizer().next_token();

  if(!directive_token.is_identifier())
    throw verilog_preprocessor_errort()
      << "expecting an identifier after backtick";

  auto &text = directive_token.text;

  if(text=="define")
  {
    if(!condition)
    {
      // ignore
      tokenizer().skip_until_eol();
      return;
    }

    // skip whitespace
    tokenizer().skip_ws();

    // we expect an identifier after `define
    const auto identifier_token = tokenizer().next_token();

    if(!identifier_token.is_identifier())
      throw verilog_preprocessor_errort()
        << "expecting an identifier after `define";

    auto &identifier = identifier_token.text;
    auto &define = defines[identifier];

    // skip whitespace
    tokenizer().skip_ws();

    // Is there a parameter list?
    // These have been introduced in Verilog 2001.
    if(tokenizer().peek() == '(')
      define.parameters = parse_define_parameters();

    // skip whitespace
    tokenizer().skip_ws();

    // Read any tokens until end of line.
    // Note that any defines in this sequence
    // are not expanded at this point.
    while(!tokenizer().eof() && tokenizer().peek() != '\n')
    {
      auto token = tokenizer().next_token();
      define.tokens.push_back(std::move(token));
    }

#ifdef DEBUG
    std::cout << "DEFINE: >" << identifier << "< = >";
    for(auto &t : define.tokens)
      std::cout << t;
    std::cout << '<' << std::endl;
#endif
  }
  else if(text=="undef")
  {
    if(!condition)
    {
      // ignore
      tokenizer().skip_until_eol();
      return;
    }

    // skip whitespace
    tokenizer().skip_ws();

    // we expect an identifier after `undef
    const auto identifier_token = tokenizer().next_token();

    if(!identifier_token.is_identifier())
      throw verilog_preprocessor_errort()
        << "expecting an identifier after `undef";

    auto &identifier = identifier_token.text;

    tokenizer().skip_until_eol();

    definest::iterator it=defines.find(identifier);

    if(it!=defines.end())
    {
      // found it! remove it!
      defines.erase(it);
    }
  }
  else if(text=="ifdef" || text=="ifndef")
  {
    bool ifdef = text == "ifdef";

    // skip whitespace
    tokenizer().skip_ws();

    // we expect an identifier
    const auto identifier_token = tokenizer().next_token();

    if(!identifier_token.is_identifier())
      throw verilog_preprocessor_errort()
        << "expecting an identifier after ifdef";

    auto &identifier = identifier_token.text;

    tokenizer().skip_until_eol();

    bool defined = defines.find(identifier) != defines.end();

    conditionalt conditional;

    if(ifdef)
      conditional.condition = defined;
    else
      conditional.condition = !defined;

    conditional.previous_condition=condition;
    conditionals.push_back(conditional);
    condition=conditional.get_cond();
  }
  else if(text=="else")
  {
    if(conditionals.empty())
      throw verilog_preprocessor_errort() << "`else without `ifdef/`ifndef";

    tokenizer().skip_until_eol();

    conditionalt &conditional=conditionals.back();

    if(conditional.else_part)
    {
      throw verilog_preprocessor_errort() << "`else without `ifdef/`ifndef";
    }

    conditional.else_part=true;
    condition=conditional.get_cond();
  }
  else if(text=="endif")
  {
    if(conditionals.empty())
    {
      throw verilog_preprocessor_errort() << "`endif without `ifdef/`ifndef";
    }

    tokenizer().skip_until_eol();

    conditionals.pop_back();

    if(conditionals.empty())
      condition=true;
    else
      condition=conditionals.back().get_cond();
  }
  else if(text=="include")
  {
    // skip whitespace
    tokenizer().skip_ws();

    // we expect a string literal
    const auto file_token = tokenizer().next_token();
    if(!file_token.is_string_literal())
      throw verilog_preprocessor_errort()
        << "expecting a string literal after `include";

    // strip quotes off string literal, escaping, etc.
    auto filename = file_token.string_literal_value();
    tokenizer().skip_until_eol();
    include(filename);
  }
  else if(text=="resetall")
  {
    // ignored
    tokenizer().skip_until_eol();
  }
  else if(text=="timescale")
  {
    // ignored
    tokenizer().skip_until_eol();
  }
  else if(text=="celldefine")
  {
    // ignored
    tokenizer().skip_until_eol();
  }
  else if(text=="endcelldefine")
  {
    // ignored
    tokenizer().skip_until_eol();
  }
  else
  {
    // check defines
    if(!condition)
      return; // ignore

    definest::const_iterator it = defines.find(text);

    if(it == defines.end())
    {
      throw verilog_preprocessor_errort()
        << "unknown preprocessor directive \"" << text << "\"";
    }

    // Found it!
    // Parse the arguments, if any.
    auto arguments = parse_define_arguments(it->second);

    // Create a new context. We then continue in that context.
    context_stack.emplace_back(it->second.tokens);
    context().define_arguments = std::move(arguments);
  }
}
