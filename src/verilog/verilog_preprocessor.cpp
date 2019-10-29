/*******************************************************************\

Module: Verilog Preprocessing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <algorithm>
#include <fstream>

#include <util/config.h>

#include "verilog_preprocessor.h"

void verilog_preprocessort::definet::replace_substring(
    std::string &source, const std::string &orig_sub,
    const std::string &new_sub) const {
  PRECONDITION(!orig_sub.empty());
  PRECONDITION(!new_sub.empty());

  std::size_t index = 0;
  auto const orig_sub_size = orig_sub.size();
  auto const new_sub_size = new_sub.size();

  while (true) {
    index = source.find(orig_sub, index);
    if (index == std::string::npos)
      break;

    source.replace(index, orig_sub_size, new_sub);
    index += new_sub_size;
  }
}

std::string verilog_preprocessort::definet::replace_macro(
    const std::string &arg_string) const {
  std::vector<std::string> arguments =
      split_string(arg_string, ',', true, true);
  PRECONDITION(arguments.size() == parameters.size());

  if (parameters.size() == 1 && parameters.back().empty())
    return value;

  auto longer_first = [](const std::string &left, const std::string &right) {
    if (left.size() > right.size())
      return true;
    return std::lexicographical_compare(left.begin(), left.end(), right.begin(),
                                        right.end());
  };

  std::map<std::string, std::string, decltype(longer_first)> param_to_arg{
      longer_first};

  for (std::size_t i = 0; i < parameters.size(); ++i) {
    param_to_arg.emplace(parameters[i], arguments[i]);
  }

  std::string result_value = value;
  for (auto const &param_arg_pair : param_to_arg) {
    replace_substring(result_value, param_arg_pair.first,
                      param_arg_pair.second);
  }
  return result_value;
}

optionalt<std::size_t>
verilog_preprocessort::find_define(const std::string &name) const {
  std::size_t define_index = 0;
  for (; define_index != defines.size(); ++define_index) {
    if (defines[define_index].identifier == name)
      return define_index;
  }
  return {};
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

Function: verilog_preprocessort::build_path

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string verilog_preprocessort::build_path(
  const std::string &path,
  const std::string &filename)
{
  if(path=="") return filename;

  if(path[path.size()-1]=='/' ||
     path[path.size()-1]=='\\')
   return path+filename;

  return path+"/"+filename;
}

/*******************************************************************\

Function: verilog_preprocessort::include

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_preprocessort::include(const std::string &filename)
{
  {
    filet tmp_file;
    files.push_back(tmp_file);
  }

  filet &file=files.back();

  file.filename=filename;
  file.close=true;

  file.in=new std::ifstream(filename.c_str());
  if(*file.in) return;

  delete file.in;
  file.close=false;

  // try include paths in given order
  for(std::list<std::string>::const_iterator
      it=config.verilog.include_paths.begin();
      it!=config.verilog.include_paths.end();
      it++)
  {
    file.close=true;
    file.in=new std::ifstream(build_path(*it, filename).c_str());
    if(*file.in) return;
    delete file.in;
    file.close=false;
  }

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
  {
    filet file;
    file.in=&in;
    file.filename=filename;
    files.push_back(file);
  }

  while(!files.empty())
  {
    files.back().print_line(out, files.size()==1?0:2);

    char ch, last_out=0;

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
          filet &file=files.back();

          if(last_out=='\n' && file.last_line!=file.line &&
             ch!='\n')
          {
            file.print_line(out, 0);
            file.last_line=file.line;
          }

          out << ch;
          last_out=ch;

          if(ch=='\n') file.last_line++;
        }
      }
    }

    if(last_out!='\n') out << '\n';
    files.pop_back();
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
      std::string arg_string;

      unsigned i_before_whitespace_skip = i;
      // skip whitespace
      while (s[i] == ' ' || s[i] == '\t' || s[i] == '\n')
        ++i;

      // maybe read the arguments
      if (s[i] == '(') {
        std::size_t level = 0;

        // find the matching parenthesis, everything between is the argument
        // list
        while (s[++i] != ')' || level != 0) {
          arg_string += s[i];

          if (s[i] == '(')
            ++level;
          else if (s[i] == ')')
            --level;
        }
        // now s[i]==')' -> let's move one more
        ++i;
      } else {
        // just in case the whitespace was important
        i = i_before_whitespace_skip;
      }

      auto maybe_define_index = find_define(text);
      if (!maybe_define_index.has_value()) {
        error() << "unknown preprocessor macro \"" << text << "\"" << eom;
        throw 0;
      }

      // found it! replace it!
      dest += defines[*maybe_define_index].replace_macro(arg_string);
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

  std::string arg_string;

  size_t unget_counter = 0;
  // skip whitespace
  while (files.back().in->get(ch)) {
    ++unget_counter;
    if (ch == ' ' || ch == '\t' || ch == '\n')
      ;
    else
      break;
  }

  // maybe read the arguments
  if (ch == '(') {
    std::size_t level = 0;

    // find the matching parenthesis, everything between is the argument
    // list
    while (files.back().in->get(ch)) {
      if (level == 0 && ch == ')') {
        break;
      }
      arg_string += ch;
      if (ch == '(')
        ++level;
      else if (ch == ')')
        --level;
    }
  } else {
    // just in case the whitespace was important
    while (unget_counter-- > 0)
      files.back().in->unget();
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

    std::string identifier, param_string, value;

    // copy identifier
    while(isalnum(*tptr) || *tptr=='$' || *tptr=='_')
    {
      identifier+=*tptr;
      tptr++;
    }

    // is there a parameter list?
    if(*tptr=='(')
    {
      while (*(++tptr) != ')')
        param_string.push_back(*tptr);
      ++tptr; // get past the closing parenthesis
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

    defines.emplace_back(identifier, param_string, value);
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

    auto maybe_define_index = find_define(identifier);
    if (maybe_define_index.has_value()) {
      defines.erase(defines.begin() + *maybe_define_index);
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

    auto maybe_define_index = find_define(identifier);

    conditionalt conditional;
    
    if(text=="ifdef")
      conditional.condition = maybe_define_index.has_value();
    else
      conditional.condition = !maybe_define_index.has_value();

    conditional.previous_condition=condition;
    conditionals.push_back(conditional);
    condition=conditional.get_cond();
  }
  else if(text=="else")
  {
    files.back().getline(line);

    if(conditionals.empty())
    {
      error() << "`else without `ifdef/`ifndef" << eom;
      throw 0;
    }

    conditionalt &conditional=conditionals.back();

    if(conditional.else_part)
    {
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
    files.back().getline(line);

    const char *tptr=line.c_str();

    // skip whitespace
    while(*tptr==' ' || *tptr=='\t') tptr++;

    if(tptr[0]!='"')
    {
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
        error() << "expected `\"'" << eom;
        throw 0;
      }

      filename+=*tptr;
      tptr++;
    }

    include(filename);
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
      auto maybe_define_index = find_define(text);
      if (!maybe_define_index.has_value()) {
        error() << "unknown preprocessor directive \"" << text << "\"" << eom;
        throw 0;
      }

      // found it! replace it!

      out << defines[*maybe_define_index].replace_macro(arg_string);
    }
  }
}
