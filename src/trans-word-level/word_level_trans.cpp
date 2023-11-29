/*******************************************************************\

Module: Word-level transition relation

Author: Daniel Kroening

Date: December 2005

Purpose:

\*******************************************************************/

#include <ostream>

#include <langapi/language_util.h>

#include "word_level_trans.h"

/*******************************************************************\

Function: word_level_transt::read_trans

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void word_level_transt::read_trans(const transt &trans)
{
  read_trans_rec(trans.trans());
}

/*******************************************************************\

Function: word_level_transt::read_trans_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void word_level_transt::read_trans_rec(const exprt &expr)
{
  PRECONDITION(expr.type().id() == ID_bool);

  if(expr.id()==ID_and)
  {
    forall_operands(it, expr)
      read_trans_rec(*it);
  }
  else if(expr.id()==ID_equal)
  {
    auto &equal_expr = to_equal_expr(expr);
    equality(equal_expr.lhs(), equal_expr.rhs());
  }
  else
    throw "word_level_transt: unexpected proposition "
          "in transition relation: "+expr.id_string();
}

/*******************************************************************\

Function: word_level_transt::equality

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void word_level_transt::equality(const exprt &lhs, const exprt &rhs)
{
  if(lhs.id()==ID_next_symbol)
  {
    const irep_idt &identifier=lhs.get(ID_identifier);
    if(next_state_functions.find(identifier)!=
       next_state_functions.end())
      throw "word_level_transt: duplicate next-state function for "+
        id2string(identifier);
    
    next_state_functions[identifier]=rhs;
  }
  else
    throw "word_level_transt: unexpected lhs "
          "in transition relation: "+lhs.id_string();
}

/*******************************************************************\

Function: word_level_transt::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void word_level_transt::output(std::ostream &out)
{
  for(next_state_functionst::const_iterator
      it=next_state_functions.begin();
      it!=next_state_functions.end();
      it++)
  {
    out << it->first << "' = ";
    out << from_expr(ns, it->first, it->second);
    out << std::endl;
  }
}

