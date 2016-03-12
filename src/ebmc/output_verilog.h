/*******************************************************************\

Module: Verilog Synthesis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iosfwd>
#include <set>

#include <util/message_stream.h>
#include <util/expr.h>

class output_verilog_baset:public message_streamt
{
public:
  output_verilog_baset(
    const symbol_tablet &_symbol_table,
    std::ostream &_out,
    message_handlert &_message_handler):
    message_streamt(_message_handler),
    symbol_table(_symbol_table), out(_out)
  {
  }

  virtual void operator()(const symbolt &symbol)=0;
  
protected:
  // common

  const symbol_tablet &symbol_table;
  std::ostream &out;
  unsigned count;

  std::string type_string_base(const typet &type);
  std::string type_string_array(const typet &type);
  void module_header(const symbolt &symbol);
  void wires(const irep_idt &module);
  void module_instantiation(const exprt &expr);

  void invariant(const exprt &expr);
  void invariants(const symbolt &symbol);
  void next_state(const exprt &expr);
  void next_state(const symbolt &symbol);
  virtual void assign_symbol(const exprt &lhs, const exprt &rhs)=0;
    
  typedef hash_set_cont<irep_idt, irep_id_hash> filest;
  void get_source_files(const exprt &expr, filest &dest);

  void source_files(const symbolt &symbol);

  std::size_t width(const exprt &expr)
  {
    return width(expr.type());
  }

  std::size_t width(const typet &type);
};

class output_verilog_netlistt:public output_verilog_baset
{
public:
  output_verilog_netlistt(
    const symbol_tablet &_symbol_table,
    std::ostream &_out,
    message_handlert &_message_handler):
    output_verilog_baset(_symbol_table, _out, _message_handler)
  {
  }

  virtual void operator()(const symbolt &symbol)
  {
    netlist(symbol);
  }
  
protected:
  void netlist(const symbolt &symbol);
  void latches(const irep_idt &module);
  virtual void assign_symbol(const exprt &lhs, const exprt &rhs);

  std::string make_symbol_expr(const exprt &expr,
                               const std::string &hint);

  bool is_symbol(const exprt &expr) const;
  std::string symbol_string(const exprt &expr);
};

class output_verilog_rtlt:public output_verilog_baset
{
public:
  output_verilog_rtlt(
    const symbol_tablet &_symbol_table,
    std::ostream &_out,
    message_handlert &_message_handler):
    output_verilog_baset(_symbol_table, _out, _message_handler)
  {
  }

  virtual void operator()(const symbolt &symbol)
  {
    rtl(symbol);
  }
  
protected:
  void rtl(const symbolt &symbol);
  void latches(const irep_idt &module);
  virtual void assign_symbol(const exprt &lhs, const exprt &rhs);
  void convert_expr(const exprt &expr);
};
