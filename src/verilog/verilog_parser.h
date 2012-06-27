/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef VERILOG_PARSER_H
#define VERILOG_PARSER_H

#include <string>

#include <parser.h>
#include <mp_arith.h>
#include "verilog_parse_tree.h"

int yyverilogparse();

class verilog_parsert:public parsert
{
public:
  verilog_parse_treet parse_tree;

  // for lexing strings
  std::string string_literal;
  
  typedef enum { LANGUAGE, EXPRESSION, TYPE } grammart;
  grammart grammar;
  
  typedef enum { STRICT_VERILOG, VIS_VERILOG, SYSTEM_VERILOG } modet;
  modet mode;
  
  virtual bool parse()
  {
    return yyverilogparse();
  }
  
  virtual void clear()
  {
    parsert::clear();
    parse_tree.clear();
  }
  
  verilog_parsert():mode(VIS_VERILOG)
  {
    dummy_id=0;
  }
  
  unsigned dummy_id;

  std::string get_dummy_id()
  {
    dummy_id++;
    return integer2string(dummy_id-1);
  }
};

extern verilog_parsert verilog_parser;

bool parse_verilog_file(const std::string &filename);
void verilog_scanner_init();

#endif
