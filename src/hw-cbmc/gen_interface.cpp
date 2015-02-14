/*******************************************************************\

Module: Variable Mapping HDL<->C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <set>
#include <sstream>

#include <util/i2string.h>
#include <util/config.h>
#include <util/arith_tools.h>
#include <util/std_types.h>

#include "gen_interface.h"

class gen_interfacet
{
public:
  gen_interfacet(const symbol_tablet &_symbol_table,
                 std::ostream &_out,
                 std::ostream &_err):
    symbol_table(_symbol_table), out(_out), err(_err) { }

  void gen_interface(const symbolt &top_module, bool have_bound);

protected:
  const symbol_tablet &symbol_table;
  std::ostream &out, &err;

  std::set<irep_idt> modules_done;
  std::set<irep_idt> modules_in_progress;

  std::map<std::string, std::string> typedef_map;
  std::stringstream stypedef;

  const symbolt &lookup(const irep_idt &identifier);
  std::string gen_declaration(const symbolt &symbol);

  void gen_module(const symbolt &module, std::ostream& os);

  std::string type_to_string(const typet& type);
};

/*******************************************************************\

Function: gen_interfacet::lookup

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const symbolt &gen_interfacet::lookup(const irep_idt &identifier)
{
  symbol_tablet::symbolst::const_iterator it=
    symbol_table.symbols.find(identifier);

  if(it==symbol_table.symbols.end())
  {
    err << "failed to find identifier " << identifier << std::endl;
    throw 0;
  }

  return it->second;
}

/*******************************************************************\

Function: gen_interfacet::gen_declaration

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string gen_interfacet::gen_declaration(const symbolt &symbol)
{
  std::string result;
  result += type_to_string(symbol.type);
  result += " ";
  result += id2string(symbol.base_name);
  return result;
}

/*******************************************************************\

Function: gen_interfacet::gen_declaration

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string gen_interfacet::type_to_string(const typet& type)
{
  if(type.id()==ID_bool)
  {
    return "_Bool";
  }
  else if(type.id()==ID_unsignedbv || type.id()==ID_signedbv)
  {
    unsigned width=
      type.id()==ID_unsignedbv?
        to_unsignedbv_type(type).get_width():
        to_signedbv_type(type).get_width();
    
    std::string sign=type.id()==ID_unsignedbv?"unsigned ":"signed ";
    
    std::string type_str=sign;
    
    // Is there some integer type that fits?
    if(width==config.ansi_c.char_width)
      type_str+="char";
    else if(width==config.ansi_c.short_int_width)
      type_str+="short int";
    else if(width==config.ansi_c.int_width)
      type_str+="int";
    else if(width==config.ansi_c.long_int_width)
      type_str+="long int";
    else if(width==config.ansi_c.long_long_int_width)
      type_str+="long long int";
    else
      type_str+="__CPROVER_bitvector["+i2string(width)+"]";
    
    std::string name="_u"+i2string(width);

    std::map<std::string,std::string>::const_iterator cit =
      typedef_map.find(type_str);
      
    if(cit!=typedef_map.end())
      return cit->second; // it's already there

    typedef_map[type_str]=name;

    stypedef << "typedef " << type_str << " " 
             << name << ";\n";

    return name;
  }
  else if(type.id()==ID_array)
  {
    const exprt &size_expr=
      to_array_type(type).size();
 
    mp_integer size = 0;
    to_integer(size_expr, size);

    std::string stype_str = type_to_string(type.subtype());
    std::string array_str = "[" + integer2string(size)+"]" ;
    std::string key_str = stype_str + array_str;

    std::map<std::string,std::string>::const_iterator cit =
      typedef_map.find(key_str);
      
    if(cit != typedef_map.end())
    {
      // it's already there
      return cit->second;
    }

    std::string new_type =
      "_array_of_" + integer2string(size) +"_" + stype_str;
    
    typedef_map[key_str] = new_type;
    
    stypedef << "typedef " << stype_str << " " << new_type
             << array_str << ";\n";
    return new_type;
  }
  else
  {
    // what else can it be?
    err << "Case " << type.id() << " not implemented";
    throw 0;
  }
}

/*******************************************************************\

Function: gen_interfacet::module_struct

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void gen_interfacet::gen_module(
  const symbolt &module,
  std::ostream &os)
{
  if(modules_done.find(module.name)!=modules_done.end())
    return;

  if(modules_in_progress.find(module.name)!=modules_in_progress.end())
  {
    err << "cyclic module instantiation in module " << module.name
        << std::endl;
    throw 0;
  }

  std::set<irep_idt>::iterator
    in_progress_it=modules_in_progress.insert(module.name).first;

  forall_symbol_module_map(it, symbol_table.symbol_module_map, module.name)
  {
    const symbolt &symbol=lookup(it->second);

    if(symbol.type.id()==ID_module_instance)
    {
      const symbolt &module_symbol=lookup(symbol.value.get(ID_module));
      gen_module(module_symbol, os);
    }
  }

  os << "// Module " << module.name << '\n'
      << "\n";

  os << "struct module_" << module.base_name << " {\n";    

  forall_symbol_module_map(it, symbol_table.symbol_module_map, module.name)
  {
    const symbolt &symbol=lookup(it->second);
    
    if(symbol.name!=id2string(module.name)+"."+id2string(symbol.base_name))
      continue;

    if(symbol.type.id()==ID_module_instance)
    {
      const symbolt &module_symbol=lookup(symbol.value.get(ID_module));

      os << "  struct module_"
         << module_symbol.base_name
         << " " << symbol.base_name;

      os << ";\n";
    }
    else if(symbol.type.id()==ID_module)
    {
    }
    else if(symbol.type.id()!=ID_integer &&
            !symbol.is_property)
    {
      os << "  " << gen_declaration(symbol)
         << ";\n";
    }
  }

  os << "};\n\n";

  modules_in_progress.erase(in_progress_it);

  modules_done.insert(module.name);
}

/*******************************************************************\

Function: gen_interfacet::gen_interface

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void gen_interfacet::gen_interface(
  const symbolt &module,
  bool has_bound)
{
  if(has_bound)
  {
    out << "/* Unwinding Bound */\n"
           "\n"
           "extern const unsigned int bound;\n"
           "\n"
           "/* Next Timeframe  */\n"
           "\n"
           "void next_timeframe(void);\n"
           "void set_inputs(void);\n";
  }

  std::stringstream smodule;
  
  gen_module(module, smodule);
  
  out << "\n"
      << "// type declarations\n";
      
  out << stypedef.str() << '\n';
  out << smodule.str() << '\n';

  out << "\n"
      << "// top module\n";
      
  out << "extern struct module_" << module.base_name << " "
      << module.base_name << ";\n";

  out << '\n';
}

/*******************************************************************\

Function: gen_interfacet::gen_interface

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void gen_interface(
  const symbol_tablet &symbol_table,
  const symbolt &top_module,
  bool have_bound,
  std::ostream &out,
  std::ostream &err)
{
  gen_interfacet gen_interface(symbol_table, out, err);
  gen_interface.gen_interface(top_module, have_bound);
}
