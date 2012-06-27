/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SMV_LANGUAGE_H
#define CPROVER_SMV_LANGUAGE_H

/*! \defgroup gr_smvlang SMV front-end */

#include <language.h>

#include "smv_parse_tree.h"

/*! \brief TO_BE_DOCUMENTED
    \ingroup gr_smvlang
*/
class smv_languaget:public languaget
{
public:
  virtual bool parse(
    std::istream &instream,
    const std::string &path,
    message_handlert &message_handler);

  virtual void dependencies(
    const std::string &module,
    std::set<std::string> &module_set);

  virtual void modules_provided(
    std::set<std::string> &module_set);
                 
  virtual bool typecheck(
    contextt &context,
    const std::string &module,
    message_handlert &message_handler);
  
  virtual void show_parse(std::ostream &out);
  
  virtual ~smv_languaget() { }
  
  virtual bool from_expr(
    const exprt &expr,
    std::string &code,
    const namespacet &ns);

  virtual bool from_type(
    const typet &type,
    std::string &code,
    const namespacet &ns);

  virtual bool to_expr(
    const std::string &code,
    const std::string &module,
    exprt &expr,
    message_handlert &message_handler,
    const namespacet &ns);
                       
  virtual std::string id() const { return "SMV"; }
  virtual std::string description() const { return "SMV"; }
  virtual std::set<std::string> extensions() const
  { std::set<std::string> s; s.insert("smv"); return s; }
  
  virtual languaget *new_language()
  { return new smv_languaget; }
     
  smv_parse_treet smv_parse_tree;
};

languaget *new_smv_language();
 
#endif
