/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_VHDL_PARSER_H
#define CPROVER_VHDL_PARSER_H

#include <util/mp_arith.h>
#include <util/parser.h>

#include <string>

#define FLEX_PREFIX yyvhdl
#include <verilog/flex_interface.h>

#include "vhdl_parse_tree.h"

#include <memory>

int yyvhdlparse();

extern class vhdl_parsert *vhdl_parser_ptr;

/// the flex-generated reentrant scanner
using vhdl_scannert = FLEX_CLASS_NAME;

class vhdl_parsert : public parsert
{
public:
  vhdl_parse_treet parse_tree;

  typedef enum
  {
    LANGUAGE,
    EXPRESSION,
    TYPE
  } grammart;
  grammart grammar;

  virtual bool parse()
  {
    PRECONDITION(in != nullptr);
    scanner = std::make_unique<vhdl_scannert>(*in);
    last_token = 0;
    bool result = yyvhdlparse();
    scanner.reset();
    return result;
  }

  // the scanner, which exists while parsing
  std::unique_ptr<vhdl_scannert> scanner;

  explicit vhdl_parsert(message_handlert &message_handler)
    : parsert(message_handler)
  {
    PRECONDITION(vhdl_parser_ptr == nullptr);
    vhdl_parser_ptr = this;
  }

  ~vhdl_parsert()
  {
    vhdl_parser_ptr = nullptr;
  }

  std::vector<std::string> comments;

  inline vhdl_parse_treet::itemt &new_item()
  {
    parse_tree.items.push_back(vhdl_parse_treet::itemt());
    return parse_tree.items.back();
  }

  inline vhdl_parse_treet::itemt &new_entity_item()
  {
    parse_tree.items.push_back(vhdl_parse_treet::itemt());
    parse_tree.items.back().set_item_type("entity");
    return parse_tree.items.back();
  }

  inline vhdl_parse_treet::itemt &new_use_item()
  {
    parse_tree.items.push_back(vhdl_parse_treet::itemt());
    parse_tree.items.back().set_item_type("use");
    return parse_tree.items.back();
  }

  inline vhdl_parse_treet::itemt &new_architecture_item()
  {
    parse_tree.items.push_back(vhdl_parse_treet::itemt());
    parse_tree.items.back().set_item_type("architecture");
    return parse_tree.items.back();
  }

  inline vhdl_parse_treet::itemt &new_package_item()
  {
    parse_tree.items.push_back(vhdl_parse_treet::itemt());
    parse_tree.items.back().set_item_type("package");
    return parse_tree.items.back();
  }

  inline vhdl_parse_treet::itemt &new_package_body_item()
  {
    parse_tree.items.push_back(vhdl_parse_treet::itemt());
    parse_tree.items.back().set_item_type("package_body");
    return parse_tree.items.back();
  }

  inline vhdl_parse_treet::itemt &new_library_item()
  {
    parse_tree.items.push_back(vhdl_parse_treet::itemt());
    parse_tree.items.back().set_item_type("library");
    return parse_tree.items.back();
  }

  struct yystypet
  {
    irep_idt text;
    irep_idt file;
    unsigned line, column;
    unsigned stack_index;

    void set_location(irept &dest)
    {
      source_locationt &loc = static_cast<exprt &>(dest).add_source_location();
      loc.set_file(file);
      loc.set_line(line);
      loc.set_column(column);
    }
  };

  inline void set_location(yystypet &dest, unsigned token_length) const
  {
    dest.file = get_file();
    dest.line = get_line_no();
    dest.column = get_column() - token_length;
  }

  /// a syntax error at the current token, with line and column
  void syntax_error(const std::string &message, const std::string &before)
  {
    source_locationt location = source_location();
    location.set_column(get_column() - before.size());
    log.error().source_location = location;
    log.error() << message;
    if(!before.empty())
      log.error() << " before `" << before << "'";
    log.error() << messaget::eom;
  }

  // for escaped identifiers and string literals
  std::string scanner_buffer;

  // the previous token, to disambiguate the tick
  int last_token = 0;
};

bool parse_vhdl_file(const std::string &filename);

#endif
