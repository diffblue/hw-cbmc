/*******************************************************************\

Module: Verilog Synthesis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cstdlib>

#include <i2string.h>
#include <arith_tools.h>
#include <simplify_expr.h>

#include <verilog/verilog_language.h>
#include <verilog/verilog_typecheck.h>
#include <verilog/verilog_synthesis.h>
#include <verilog/expr2verilog_class.h>
#include <verilog/expr2verilog.h>

#include "output_verilog.h"

/*******************************************************************\

Function: output_verilog_baset::width

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

unsigned output_verilog_baset::width(const typet &type)
{
  if(type.id()==ID_bool)
    return 1;
    
  if(type.id()==ID_unsignedbv || type.id()==ID_signedbv)
    return atoi(type.get(ID_width).c_str());
  
  std::cerr << type.id() << std::endl;
  assert(false);
  
  return 0; // not reached
}

/*******************************************************************\

Function: output_verilog_netlistt::is_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool output_verilog_netlistt::is_symbol(const exprt &expr) const
{
  if(expr.id()==ID_extractbit ||
     expr.id()==ID_extractbits)
  {
    assert(expr.operands().size()>=1);
    return is_symbol(expr.op0());
  }
  else if(expr.id()==ID_symbol)
  {
    return true;
  }
  
  return false;
}

/*******************************************************************\

Function: output_verilog_netlistt::make_symbol_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string output_verilog_netlistt::make_symbol_expr(
  const exprt &expr,
  const std::string &hint)
{
  if(is_symbol(expr))
    return symbol_string(expr);

  if(expr.is_constant())
  {
    mp_integer i;
    if(to_integer(expr, i))
    {
      str << "failed to convert constant: " << expr.pretty() << std::endl;
      throw 0;
    }
    
    unsigned w=width(expr);
    return i2string(w)+"'b"+integer2binary(i, w);
  }
  
  return "TODO";
}

/*******************************************************************\

Function: output_verilog_netlistt::assign_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

struct subst_map_entryt
{
  const char *a, *b;
} subst_map[]=
{
  { ">",  "gt" },
  { ">=", "ge" },
  { "<",  "lt" },
  { "<=", "le" },
  { "=",  "eq" },
  { "notequal", "ne" },
  { "unary-", "unary_minus" },
  { NULL, NULL }
};

void output_verilog_netlistt::assign_symbol(
  const exprt &lhs,
  const exprt &rhs)
{
  if(rhs.location().is_not_nil())
    out << "  // " << rhs.location() << std::endl;

  if(is_symbol(rhs))
  {
    out << "  wire "
        << symbol_string(lhs) << " = "
        << symbol_string(rhs) << ";" << std::endl << std::endl;
  }
  else if(rhs.is_constant())
  {
    out << "  wire "
        << symbol_string(lhs) << " = "
        << make_symbol_expr(rhs, "") << ";" << std::endl << std::endl;
  }
  else if(rhs.id()==ID_and ||
          rhs.id()==ID_or ||
          rhs.id()==ID_nand ||
          rhs.id()==ID_nor ||
          rhs.id()==ID_xor ||
          rhs.id()=="xnor")
  {
    assert(rhs.type().id()==ID_bool);
    assert(lhs.type().id()==ID_bool);

    std::string tmp;
    
    forall_operands(it, rhs)
    {
      tmp+=", ";
      tmp+=make_symbol_expr(*it, "");
    }
    
    out << "  " << rhs.id() << " g" << (++count) << "("
        << symbol_string(lhs) << tmp
        << ");" << std::endl << std::endl;
  }
  else if(rhs.id()=="not")
  {
    assert(rhs.type().id()==ID_bool);
    assert(lhs.type().id()==ID_bool);
    assert(rhs.operands().size()==1);

    std::string tmp=make_symbol_expr(rhs.op0(), "");
    
    out << "  " << rhs.id() << " g" << (++count) << "("
        << symbol_string(lhs) << tmp
        << ");" << std::endl << std::endl;
  }
  else if(rhs.id()=="+" || 
          rhs.id()=="-" ||
          rhs.id()=="*")
  {
    if(rhs.operands().size()==1)
      assign_symbol(lhs, rhs.op0());
    else
    {
      std::string tmp;

      assert(rhs.operands().size()!=0);

      if(rhs.operands().size()==2)
        tmp=make_symbol_expr(rhs.op0(), "")+", "+
            make_symbol_expr(rhs.op1(), "");
      else
      {
        exprt tmp_rhs(rhs);
        tmp_rhs.operands().erase(tmp_rhs.operands().begin());
        
        tmp=make_symbol_expr(rhs.op0(), "")+", "+
            make_symbol_expr(tmp_rhs, "");
      }
    
      out << "  RTL_";

      if(rhs.id()=="+")
        out << "add";
      else if(rhs.id()=="-")
        out << "sub";
      else
        out << "mult";

      out << " #(" 
          << width(rhs) << ") m" << (++count) << "(" << tmp 
          << ");" << std::endl << std::endl;        
    }
  }
  else
  {
    struct subst_map_entryt *p=subst_map;

    while(p->a!=NULL)
    {
      if(rhs.id()==subst_map->a)
      {
        out << "  RTL_" << subst_map->b << " #(" 
            << width(rhs) << ") m" << (++count) << "(";
            
        forall_operands(it, rhs)
        {
          if(it!=rhs.operands().begin()) out << ", ";
          make_symbol_expr(*it, "");
        }
        
        out << ");" << std::endl << std::endl;        
      }

      p++;
    }

    err_location(rhs);    
    str << "unexpected operator: " << rhs.id() << std::endl;
    throw 0;
  }
}

/*******************************************************************\

Function: output_verilog_rtlt::assign_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void output_verilog_rtlt::assign_symbol(
  const exprt &lhs,
  const exprt &rhs)
{
  if(lhs.id()=="extractbits")
  {
    assert(lhs.operands().size()==3);

    // redundant?
    mp_integer from, to;

    if(!to_integer(lhs.op1(), to) &&
       !to_integer(lhs.op2(), from))
    {
      if(from==0 &&
         to==width(lhs.op0().type())-1)
      {
        assign_symbol(lhs.op0(), rhs);
        return;
      }
    }
  }

  if(rhs.location().is_not_nil())
    out << "  // " << rhs.location() << std::endl;

  exprt symbol_expr=lhs;

  if(lhs.id()=="extractbit")
  {
    if(lhs.operands().size()!=2)
    {
      err_location(lhs);
      str << "extractbit takes two operands";
      throw 0;
    }

    symbol_expr=lhs.op0();
  }
  else if(lhs.id()=="extractbits")
  {
    if(lhs.operands().size()!=3)
    {
      err_location(lhs);
      str << "extractbits takes three operands";
      throw 0;
    }

    symbol_expr=lhs.op0();
  }

  if(symbol_expr.id()!="symbol" &&
     symbol_expr.id()!="next_symbol")
  {
    err_location(lhs);
    str << "assign_symbol expects symbol on lhs, but got `";
    str << expr2verilog(symbol_expr) << "'";
    throw 0;
  }
  
  const symbolt &symbol=namespacet(context).lookup(symbol_expr);
  
  if(symbol.is_state_var)
  {
    out << "  always @(";
    out << "posedge clock";
    out << ")" << std::endl;
    out << "    ";

    // replace the next_symbol
    exprt tmp(lhs);
    if(tmp.id()=="extractbit" || tmp.id()=="extractbits")
      tmp.op0().id("symbol");
    else
      tmp.id("symbol");

    convert_expr(tmp);
    out << " <= ";
    convert_expr(rhs);
    out << ";" << std::endl;
  }
  else
  {
    out << "  assign ";
    convert_expr(lhs);
    out << " = ";
    convert_expr(rhs);
    out << ";" << std::endl;
  }
  
  out << std::endl;
}

/*******************************************************************\

Function: output_verilog_rtlt::convert_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void output_verilog_rtlt::convert_expr(const exprt &expr)
{
  expr2verilogt expr2verilog;

  // simplify first
  namespacet ns(context);
  exprt tmp(expr);
  simplify(tmp,ns);
  
  out << expr2verilog.convert(tmp);
}

/*******************************************************************\

Function: output_verilog_netlistt::symbol_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string output_verilog_netlistt::symbol_string(const exprt &expr)
{
  std::string result;
  
  if(expr.id()==ID_extractbit)
  {
    assert(expr.operands().size()==2);

    mp_integer i;
    if(to_integer(expr.op1(), i))
    {
      err_location(expr.op1());
      str << "failed to convert constant "
          << expr.op1() << std::endl;
      throw 0;
    }

    unsigned offset=atoi(expr.op0().type().get("#offset").c_str());
    
    assert(i>=offset);
    
    return
      symbol_string(expr.op0())+
      "["+integer2string(i-offset)+"]";
  }
  else if(expr.id()==ID_extractbits)
  {
    assert(expr.operands().size()==3);

    mp_integer from;
    if(to_integer(expr.op1(), from))
    {
      err_location(expr.op1());
      str << "failed to convert constant "
          << expr.op1() << std::endl;
      throw 0;
    }

    mp_integer to;
    if(to_integer(expr.operands()[2], to))
    {
      err_location(expr.operands()[2]);
      str << "failed to convert constant "
          << expr.operands()[2] << std::endl;
      throw 0;
    }

    unsigned offset=atoi(expr.op0().type().get("#offset").c_str());
    
    assert(from>=offset);
    assert(to>=offset);
    
    assert(to>=from);
    
    return
      symbol_string(expr.op0())+
      "["+integer2string(to-offset)+
      ":"+integer2string(from-offset)+"]";
  }
  else if(expr.id()==ID_symbol)
  {
    const irep_idt &identifier=expr.get(ID_identifier);
    contextt::symbolst::const_iterator s_it=
      context.symbols.find(identifier);
    
    if(s_it==context.symbols.end())
    {
      err_location(expr);
      str << "symbol " << identifier << " not found"
          << std::endl;
      throw 0;
    }
    
    const symbolt &symbol=s_it->second;
    return id2string(symbol.base_name);
  }
  else if(expr.id()==ID_nondet_symbol)
  {
    const irep_idt &identifier=expr.get(ID_identifier);
    return id2string(identifier);
  }
  else if(expr.id()==ID_next_symbol)
  {
    const irep_idt &identifier=expr.get(ID_identifier);
    contextt::symbolst::const_iterator s_it=
      context.symbols.find(identifier);
    
    if(s_it==context.symbols.end())
    {
      err_location(expr);
      str << "symbol " << identifier << " not found"
          << std::endl;
      throw 0;
    }
    
    const symbolt &symbol=s_it->second;
    return "next_"+id2string(symbol.base_name);
  }

  err_location(expr);
  str << "Not a symbol: " << expr.pretty() << std::endl;
  throw 0;
}

/*******************************************************************\

Function: output_verilog_baset::type_string_base

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string output_verilog_baset::type_string_base(const typet &type)
{
  std::string type_string;

  if(type.id()==ID_bool)
    return "";
  else if(type.id()=="unsignedbv")
  {
    unsigned width=atoi(type.get("width").c_str());
    unsigned offset=atoi(type.get("#offset").c_str());
    
    type_string="["+i2string(width-1+offset)+":"+
                    i2string(offset)+"]";

    return type_string;
  }
  else if(type.id()=="array")
  {
    return type_string_base(type.subtype());
  }
  else
  {
    err_location(type);
    str << "failed to convert type "
        << type.pretty() << std::endl;
    throw 0;
  }

  return "";
}

/*******************************************************************\

Function: output_verilog_baset::type_string_array

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string output_verilog_baset::type_string_array(const typet &type)
{
  if(type.id()=="array")
  {
    mp_integer size;
    to_integer(static_cast<const exprt &>(type.find("size")), size);
    return type_string_array(type.subtype())+" [0:"+integer2string(size)+"]";
  }

  return "";
}

/*******************************************************************\

Function: output_verilog_baset::module_header

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void output_verilog_baset::module_header(const symbolt &symbol)
{
  out << "module " << symbol.base_name;

  const irept &ports=symbol.type.find("ports");
  
  //
  // print port in module statement
  //
  if(!ports.get_sub().empty())
  {
    out << "(";

    forall_irep(it, ports.get_sub())
    {
      if(it!=ports.get_sub().begin())
        out << ", ";

      out << it->get("#name");
    }

    out << ")";
  }

  out << ";" << std::endl;

  out << std::endl;

  //
  // port declarations
  //
  forall_irep(it, ports.get_sub())
  {
    bool is_input=it->get_bool("input");
    bool is_output=it->get_bool("output");
    
    out << "  ";
    
    if(is_input && is_output)
      out << "inout";
    else if(is_input)
      out << "input";
    else
      out << "output";

    const typet &type=static_cast<const typet &>(it->find("type"));

    const std::string type_str_base=type_string_base(type);
    const std::string type_str_array=type_string_array(type);

    out << " " << type_str_base;
    if(!type_str_base.empty()) out << " ";
    out << it->get("#name") << type_str_array << ";" << std::endl;
  }

  out << std::endl;
}                        

/*******************************************************************\

Function: output_verilog_netlistt::latches

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void output_verilog_netlistt::latches(const irep_idt &module)
{
  bool found=false;

  forall_symbol_module_map(m_it, context.symbol_module_map, module)
  {
    const irep_idt &identifier=m_it->second;
    
    contextt::symbolst::const_iterator s_it=
      context.symbols.find(identifier);
    
    if(s_it==context.symbols.end())
    {
      str << "failed to find symbol " << identifier
          << std::endl;
      throw 0;
    }

    const symbolt &symbol=s_it->second;
    
    if(symbol.is_state_var)
    {
      out << "  ";
      out << "DFF l" << ++count;
      out << type_string_base(symbol.type);

      out << " (" << symbol.base_name; // D
      out << ", next_" << symbol.base_name; // Q
      out << ", "; // clk
      
      out << ");" << std::endl;
      
      found=true;
    }
  }
  
  if(found) out << std::endl;
}

/*******************************************************************\

Function: output_verilog_rtlt::latches

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void output_verilog_rtlt::latches(const irep_idt &module)
{
  bool found=false;

  forall_symbol_module_map(m_it, context.symbol_module_map, module)
  {
    const irep_idt &identifier=m_it->second;
    
    contextt::symbolst::const_iterator s_it=
      context.symbols.find(identifier);
    
    if(s_it==context.symbols.end())
    {
      str << "failed to find symbol " << identifier
          << std::endl;
      throw 0;
    }

    const symbolt &symbol=s_it->second;
    
    if(symbol.is_state_var)
    {
      const std::string type_base=type_string_base(symbol.type);
      const std::string type_array=type_string_array(symbol.type);
    
      out << "  reg " << type_base;
      if(type_base!="") out << " ";
      
      out << symbol.base_name << type_array << ";" << std::endl;
      found=true;
    }
  }
  
  if(found) out << std::endl;
}

/*******************************************************************\

Function: output_verilog_baset::wires

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void output_verilog_baset::wires(const irep_idt &module)
{
  bool found=false;

  forall_symbol_module_map(m_it, context.symbol_module_map, module)
  {
    const irep_idt &identifier=m_it->second;
    
    contextt::symbolst::const_iterator s_it=
      context.symbols.find(identifier);
    
    if(s_it==context.symbols.end())
    {
      str << "failed to find symbol " << identifier
          << std::endl;
      throw 0;
    }

    const symbolt &symbol=s_it->second;
    
    if(!symbol.is_state_var &&
       !symbol.is_input &&
       !symbol.is_output &&
       !symbol.is_property &&
       !symbol.is_macro &&
       symbol.type.id()!=ID_integer &&
       symbol.type.id()!=ID_module &&
       symbol.type.id()!=ID_module_instance &&
       symbol.type.id()!=ID_code)
    {
      const std::string type_base=type_string_base(symbol.type);
      out << "  ";
      out << "wire " << type_base << (type_base==""?"":" ")
          << symbol.base_name << ";" << std::endl;
      found=true;
    }
  }
  
  if(found) out << std::endl;
}

/*******************************************************************\

Function: output_verilog_baset::module_instantiation

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void output_verilog_baset::module_instantiation(const exprt &expr)
{
  assert(expr.type().id()==ID_bool);

  std::list<std::string> argument_strings;

  #if 0  
  std::string hint("argument");
  const irep_idt &instance=expr.get("instance");
  if(!instance.empty()) hint+="_"+id2string(instance);
  
  forall_operands(it, expr)
    argument_strings.push_back(make_symbol_expr(*it, hint));
  #endif

  out << "  // Module instantiation " << expr.location() << std::endl;
  out << "  " << expr.get("module") << " ";
  out << expr.get("instance");

  out << "(";

  for(std::list<std::string>::const_iterator
      it=argument_strings.begin();
      it!=argument_strings.end();
      it++)
  {
    if(it!=argument_strings.begin())
      out << ", ";
      
    out << *it;
  }
  
  out << ");" << std::endl;
  out << std::endl;
}

/*******************************************************************\

Function: output_verilog_baset::invariant

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void output_verilog_baset::invariant(const exprt &expr)
{
  assert(expr.type().id()==ID_bool);
  
  if(expr.id()==ID_and)
  {
    forall_operands(it, expr)
      invariant(*it);
  }
  else if(expr.id()=="module-instantiation" ||
          expr.id()=="verilog-primitive-module")
  {
    module_instantiation(expr);
  }
  else if(expr.is_true())
  {
    // nothing to do
  }
  else if(expr.id()=="=")
  {
    assert(expr.operands().size()==2);
    assign_symbol(expr.op0(), expr.op1());
  }
  else
  {
    std::cout << "Unexpected invariant: " << expr.pretty() << std::endl;
    throw 0;
  }
}

/*******************************************************************\

Function: output_verilog_baset::invariants

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void output_verilog_baset::invariants(const symbolt &symbol)
{
  assert(symbol.value.id()=="trans" &&
         symbol.value.operands().size()==3);

  invariant(symbol.value.op0());
}

/*******************************************************************\

Function: output_verilog_baset::next_state

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void output_verilog_baset::next_state(const exprt &expr)
{
  assert(expr.type().id()==ID_bool);
  
  if(expr.id()==ID_and)
  {
    forall_operands(it, expr)
      next_state(*it);
    return;
  }
  else if(expr.is_true())
    return;

  assert(expr.id()=="=");
  assert(expr.operands().size()==2);

  assign_symbol(expr.op0(), expr.op1());  
}

/*******************************************************************\

Function: output_verilog_baset::next_state

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void output_verilog_baset::next_state(const symbolt &symbol)
{
  assert(symbol.value.id()=="trans" &&
         symbol.value.operands().size()==3);

  next_state(symbol.value.operands()[2]);
}

/*******************************************************************\

Function: output_verilog_netlistt::netlist

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void output_verilog_netlistt::netlist(const symbolt &symbol)
{
  count=0;

  out << "//" << std::endl;
  out << "// Module: " << symbol.base_name << std::endl;
  out << "// " << symbol.location << std::endl;
  out << "//" << std::endl;
  out << std::endl;
  
  source_files(symbol);
  module_header(symbol);
  wires(symbol.module);
  latches(symbol.module);
  invariants(symbol);  
  next_state(symbol);

  out << "endmodule // end of " << symbol.base_name << std::endl;
  out << std::endl;
}                        

/*******************************************************************\

Function: output_verilog_rtlt::rtl

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void output_verilog_rtlt::rtl(const symbolt &symbol)
{
  count=0;

  out << "//" << std::endl;
  out << "// Module: " << symbol.base_name << std::endl;
  out << "// " << symbol.location << std::endl;
  out << "//" << std::endl;
  out << std::endl;

  source_files(symbol);
  module_header(symbol);
  wires(symbol.module);
  latches(symbol.module);
  invariants(symbol);  
  next_state(symbol);

  out << "endmodule // end of " << symbol.base_name << std::endl;
  out << std::endl;
}                        

/*******************************************************************\

Function: output_verilog_baset::source_files

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void output_verilog_baset::source_files(
  const symbolt &symbol)
{
  filest files;

  get_source_files(symbol.value, files);
  
  if(symbol.location.get_file()!="")
    files.insert(symbol.location.get_file());

  out << "// Source files:" << std::endl;

  for(filest::const_iterator
      it=files.begin();
      it!=files.end();
      it++)
  {
    if((*it)!="" && (*it)[0]!='<')
      out << "//   " << *it << std::endl;
  }

  out << std::endl;  
}

/*******************************************************************\

Function: output_verilog_baset::get_source_files

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void output_verilog_baset::get_source_files(
  const exprt &expr,
  filest &files)
{
  const irep_idt &file=expr.location().get_file();
  
  if(file!="")
    files.insert(file);

  forall_operands(it, expr)
    get_source_files(*it, files);
}

