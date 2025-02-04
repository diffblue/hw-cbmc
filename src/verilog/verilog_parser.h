/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef VERILOG_PARSER_H
#define VERILOG_PARSER_H

#include <util/mp_arith.h>
#include <util/parser.h>

#include "verilog_parse_tree.h"
#include "verilog_scanner.h"
#include "verilog_scope.h"
#include "verilog_standard.h"

#include <map>
#include <string>

int yyverilogparse();

extern class verilog_parsert *verilog_parser_ptr;

class verilog_parsert:public parsert
{
public:
  verilog_parse_treet parse_tree;

  // scanner state
  verilog_scannert scanner;

  typedef enum { LANGUAGE, EXPRESSION, TYPE } grammart;
  grammart grammar;

  virtual bool parse()
  {
    return yyverilogparse()!=0;
  }

  explicit verilog_parsert(
    verilog_standardt standard,
    message_handlert &message_handler)
    : parsert(message_handler), parse_tree(standard), scanner(standard)
  {
    PRECONDITION(verilog_parser_ptr == nullptr);
    verilog_parser_ptr = this;
  }

  ~verilog_parsert()
  {
    verilog_parser_ptr = nullptr;
  }

  // parser scopes and identifiers
  using scopet = verilog_scopet;

  verilog_scopest scopes;

  // These are used for anonymous gate instances
  // and to create a unique identifier for enum types.
  std::size_t next_id_counter = 0;

  std::string get_next_id()
  {
    next_id_counter++;
    return integer2string(next_id_counter - 1);
  }
};

bool parse_verilog_file(const std::string &filename, verilog_standardt);
void verilog_scanner_init();

#endif
