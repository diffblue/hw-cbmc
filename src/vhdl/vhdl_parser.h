/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef VHDL_PARSER_H
#define VHDL_PARSER_H

#include <string>

#include <parser.h>
#include <mp_arith.h>
#include "vhdl_parse_tree.h"

int yyvhdlparse();

class vhdl_parsert:public parsert
{
public:
  vhdl_parse_treet parse_tree;

  typedef enum { LANGUAGE, EXPRESSION, TYPE } grammart;
  grammart grammar;  

  virtual bool parse()
  {
    return yyvhdlparse();
  }
  
  virtual void clear()
  {
    parsert::clear();
    parse_tree.clear();
  }
  
  vhdl_parsert()
  {
  }
  
  std::vector<std::string> comments;
};

extern vhdl_parsert vhdl_parser;

bool parse_vhdl_file(const std::string &filename);
void vhdl_scanner_init();

#endif
