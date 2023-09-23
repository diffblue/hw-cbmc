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

Function: verilog_preprocessort::filet::make_source_location

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

source_locationt verilog_preprocessort::filet::make_source_location() const
{
  source_locationt result;

  result.set_file(filename);
  result.set_line(tokenizer.line_no());

  return result;
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
      files.emplace_back(true, in, filename);
      files.back().print_line_directive(out, 1); // 'enter'
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
      files.emplace_back(true, in, filename);
      files.back().print_line_directive(out, 1); // 'enter'
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
    files.emplace_back(false, &in, filename);

    files.back().print_line_directive(out, 0); // 'neither'

    while(!files.empty())
    {
      while(!tokenizer().eof())
      {
        auto token = tokenizer().next_token();
        if(token == '`')
          directive();
        else if(condition)
        {
          out << token;
        }
      }

      files.pop_back();

      if(!files.empty())
        files.back().print_line_directive(out, 2); // 'exit'
    }
  }
  catch(const verilog_preprocessor_errort &e)
  {
    if(!files.empty())
      error().source_location = files.back().make_source_location();
    error() << e.what() << eom;
    throw 0;
  }
}

/*******************************************************************\

Function: verilog_preprocessort::replace_macros

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_preprocessort::replace_macros(std::string &s)
{
  std::string dest;

  for(unsigned i=0; i<s.size();)
  {
    if(s[i]=='`')
    {
      i++;
      unsigned start=i;

      while(i<s.size() && 
            (isalnum(s[i]) || s[i]=='$' || s[i]=='_'))
        i++;

      std::string text(s, start, i-start);

      definest::const_iterator it=defines.find(text);

      if(it==defines.end())
      {
        error() << "unknown preprocessor macro \"" << text << "\"" << eom;
        throw 0;
      }

      // found it! replace it!

      dest+=it->second;
    }
    else
    {
      dest+=s[i];
      i++;
    }
  }

  dest.swap(s);
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
  auto directive_token = tokenizer().next_token();
  if(!directive_token.is_identifier())
    throw verilog_preprocessor_errort()
      << "expecting an identifier after backtick";

  const auto &text = directive_token.text;

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
    auto identifier_token = tokenizer().next_token();
    if(!identifier_token.is_identifier())
      throw verilog_preprocessor_errort()
        << "expecting an identifier after `define";

    auto &identifier = identifier_token.text;

    // Is there a parameter list?
    // These have been introduced in Verilog 2001.
    if(tokenizer().peek() == '(')
    {
      throw verilog_preprocessor_errort()
        << "`define with parameters not yet supported";
    }

    // skip whitespace
    tokenizer().skip_ws();

    // read any tokens until end of line
    std::string value;
    while(!tokenizer().eof())
    {
      auto token = tokenizer().next_token();
      if(token.is_identifier())
      {
        value += token.text;
      }
      else if(token == '\n')
        break;
      else
      {
        value += token.text;
      }
    }

#ifdef DEBUG
    std::cout << "DEFINE: >" << identifier
              << "< = >" << value << "<" << std::endl;
    #endif

    defines[identifier]=value;
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
    auto identifier_token = tokenizer().next_token();
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
    auto identifier_token = tokenizer().next_token();
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
    auto file_token = tokenizer().next_token();
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

    if(condition)
    {
      definest::const_iterator it=defines.find(text);

      if(it==defines.end())
      {
        throw verilog_preprocessor_errort()
          << "unknown preprocessor directive \"" << text << "\"";
      }

      // found it! replace it!
      out << it->second;
    }
  }
}
