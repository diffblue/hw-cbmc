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
  result.set_line(line);

  return result;
}

/*******************************************************************\

Function: verilog_preprocessort::getline

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_preprocessort::filet::getline(std::string &dest)
{
  dest="";

  char ch;

  while(get(ch) && ch!='\n')
    if(ch!='\r')
      dest+=ch;
}

/*******************************************************************\

Function: verilog_preprocessort::filet::get

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool verilog_preprocessort::filet::get(char &ch)
{
  state=INITIAL;

  while(in->get(ch))
  {
    if(ch=='\n')
    {
      line++;
      column=1;
    }
    else
      column++;

    switch(state)
    {
     case INITIAL:
      switch(ch)
      {
       case '/':
        state=DASH;
        break;

       default:
        return true;
      }
      break;

     case DASH:
      switch(ch)
      {
       case '*':
        state=C_COMMENT;
        break;

       case '/':
        state=CPP_COMMENT;
        cpp_comment_empty=(column==3);
        break;

       default:
        in->unget();
        ch='/';
        return true;
      }
      break;

     case C_COMMENT:
      switch(ch)
      {
       case '*':
        state=C_COMMENT2;
        break;

       default:;
      }
      break;

     case C_COMMENT2:
      switch(ch)
      {
       case '/':
        state=INITIAL;
        break;

       case '*':
        break;

       default:
        state=C_COMMENT;
      }
      break;

     case CPP_COMMENT:
      switch(ch)
      {
       case '\n':
        if(cpp_comment_empty)
        {
          state=INITIAL;
          break;
        }

        return true;

       default:;
      }
      break;
    }
  }

  return false;
}

/*******************************************************************\

Function: verilog_preprocessort::include

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_preprocessort::include(
  const std::string &filename,
  const source_locationt &source_location)
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
      return; // done
    }

    delete in;
  }

  error().source_location = source_location;
  error() << "include file `" << filename << "' not found" << eom;
  throw 0;
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

    while(!files.empty())
    {
      files.back().print_line(out, files.size() == 1 ? 0 : 2);

      char ch, last_out = 0;

      while(files.back().get(ch))
      {
        switch(ch)
        {
        case '`':
          directive();
          break;

        default:
          if(condition)
          {
            filet &file = files.back();

            if(last_out == '\n' && file.last_line != file.line && ch != '\n')
            {
              file.print_line(out, 0);
              file.last_line = file.line;
            }

            out << ch;
            last_out = ch;

            if(ch == '\n')
              file.last_line++;
          }
        }
      }

      if(last_out != '\n')
        out << '\n';
      files.pop_back();
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
  // remember the source location
  auto source_location = files.back().make_source_location();

  std::string text;

  char ch;

  while(files.back().in->get(ch))
  {
    if(isalnum(ch) || ch=='$' || ch=='_')
      text+=ch;
    else
    {
      files.back().in->unget();
      break;
    }
  }

  std::string line;

  if(text=="define")
  {
    files.back().getline(line);

    if(!condition)
      return;

    const char *tptr=line.c_str();

    // skip whitespace
    while(*tptr==' ' || *tptr=='\t') tptr++;

    std::string identifier, value;

    // copy identifier
    while(isalnum(*tptr) || *tptr=='$' || *tptr=='_')
    {
      identifier+=*tptr;
      tptr++;
    }

    // is there a parameter list?
    if(*tptr=='(')
    {
      error().source_location = source_location;
      error() << "`define with parameters not yet supported" << eom;
      throw 0;
    }

    // skip whitespace
    while(*tptr==' ' || *tptr=='\t') tptr++;

    value=tptr;

    // remove trailing whitespace

    while(value.size()!=0 &&
          (value[value.size()-1]==' ' || value[value.size()-1]=='\t'))
      value.resize(value.size()-1);

    replace_macros(value);

    #ifdef DEBUG
    std::cout << "DEFINE: >" << identifier
              << "< = >" << value << "<" << std::endl;
    #endif

    defines[identifier]=value;
  }
  else if(text=="undef")
  {
    files.back().getline(line);

    if(!condition)
      return;

    const char *tptr=line.c_str();

    // skip whitespace
    while(*tptr==' ' || *tptr=='\t') tptr++;

    std::string identifier, value;

    // copy identifier
    while(isalnum(*tptr) || *tptr=='$' || *tptr=='_')
    {
      identifier+=*tptr;
      tptr++;
    }

    definest::iterator it=defines.find(identifier);

    if(it!=defines.end())
    {
      // found it! remove it!

      defines.erase(it);
    }
  }
  else if(text=="ifdef" || text=="ifndef")
  {
    files.back().getline(line);

    const char *tptr=line.c_str();

    // skip whitespace
    while(*tptr==' ' || *tptr=='\t') tptr++;

    std::string identifier, value;

    // copy identifier
    while(isalnum(*tptr) || *tptr=='$' || *tptr=='_')
    {
      identifier+=*tptr;
      tptr++;
    }

    definest::iterator it=defines.find(identifier);

    conditionalt conditional;
    
    if(text=="ifdef")
      conditional.condition=(it!=defines.end());
    else
      conditional.condition=(it==defines.end());
    
    conditional.previous_condition=condition;
    conditionals.push_back(conditional);
    condition=conditional.get_cond();
  }
  else if(text=="else")
  {
    files.back().getline(line);

    if(conditionals.empty())
    {
      error().source_location = source_location;
      error() << "`else without `ifdef/`ifndef" << eom;
      throw 0;
    }

    conditionalt &conditional=conditionals.back();

    if(conditional.else_part)
    {
      error().source_location = source_location;
      error() << "`else without `ifdef/`ifndef" << eom;
      throw 0;
    }

    conditional.else_part=true;
    condition=conditional.get_cond();
  }
  else if(text=="endif")
  {
    files.back().getline(line);

    if(conditionals.empty())
    {
      error().source_location = source_location;
      error() << "`endif without `ifdef/`ifndef" << eom;
      throw 0;
    }

    conditionals.pop_back();

    if(conditionals.empty())
      condition=true;
    else
      condition=conditionals.back().get_cond();
  }
  else if(text=="include")
  {
    // remember the source location
    auto include_source_location = files.back().make_source_location();

    files.back().getline(line);

    const char *tptr=line.c_str();

    // skip whitespace
    while(*tptr==' ' || *tptr=='\t') tptr++;

    if(tptr[0]!='"')
    {
      error() << include_source_location;
      error() << "expected file name" << eom;
      throw 0;
    }

    tptr++;

    std::string filename;

    // copy filename
    while(*tptr!='"')
    {
      if(*tptr==0)
      {
        error() << include_source_location;
        error() << "expected `\"'" << eom;
        throw 0;
      }

      filename+=*tptr;
      tptr++;
    }

    include(filename, include_source_location);
  }
  else if(text=="resetall")
  {
    // ignored
    files.back().getline(line);
  }
  else if(text=="timescale")
  {
    // ignored
    files.back().getline(line);
  }
  else if(text=="celldefine")
  {
    // ignored
    files.back().getline(line);
  }
  else if(text=="endcelldefine")
  {
    // ignored
    files.back().getline(line);
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
