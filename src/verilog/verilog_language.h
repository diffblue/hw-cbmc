/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_VERILOG_LANGUAGE_H
#define CPROVER_VERILOG_LANGUAGE_H

#include <options.h>

#include "language.h"
#include "verilog_parse_tree.h"

class verilog_languaget:public languaget
{
public:
  virtual bool preprocess(
    std::istream &instream,
    const std::string &path,
    std::ostream &outstream,
    message_handlert &message_handler);

  virtual bool parse(
    std::istream &instream,
    const std::string &path,
    message_handlert &message_handler);
             
  virtual void dependencies(
    const std::string &module,
    std::set<std::string> &module_set);
                            
  virtual void modules_provided(
    std::set<std::string> &module_set);

  virtual bool interfaces(
    contextt &context,
    message_handlert &message_handler);

  virtual bool typecheck(
    contextt &context,
    const std::string &module,
    message_handlert &message_handler);
  
  virtual void show_parse(std::ostream &out);
  
  virtual ~verilog_languaget() { }
  
  virtual bool from_expr(
    const exprt &expr, std::string &code,
    const namespacet &ns);

  virtual bool from_type(
    const typet &type, std::string &code,
    const namespacet &ns);

  virtual bool to_expr(
    const std::string &code,
    const std::string &module,
    exprt &expr,
    message_handlert &message_handler,
    const namespacet &ns);

  virtual languaget *new_language()
  { return new verilog_languaget; }
   
  virtual std::string id() const { return "Verilog"; }
  virtual std::string description() const { return "Verilog"; }
  virtual std::set<std::string> extensions() const
  { std::set<std::string> s;
    s.insert("v");
    s.insert("sv");
    return s; }

  verilog_parse_treet &get_parse_tree()
  {
    return parse_tree;
  }
  
  optionst options;
  
  verilog_languaget()
  {
    options.set_option("flatten_hierarchy", true);
  }

protected:
  verilog_parse_treet parse_tree;
};
 
languaget *new_verilog_language();

#endif
