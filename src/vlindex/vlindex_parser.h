/*******************************************************************\

Module: Verilog Indexer Parser

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef VLINDEX_PARSER_H
#define VLINDEX_PARSER_H

#include <verilog/verilog_parser.h>
#include <verilog/verilog_y.tab.h>

#include "verilog_indexer.h"

#include <deque>

class verilog_indexer_parsert
{
public:
  explicit verilog_indexer_parsert(
    std::istream &in,
    verilog_indexert &__indexer,
    verilog_standardt standard,
    message_handlert &message_handler)
    : indexer(__indexer), verilog_parser(standard, message_handler)
  {
    verilog_parser.in = &in;
    verilog_parser.grammar = verilog_parsert::LANGUAGE;
  }

  // grammar rules
  void rDescription();

protected:
  using idt = verilog_indexert::idt;
  verilog_indexert &indexer;
  irep_idt current_module;

  // modules, classes, primitives, packages, interfaces, configurations
  void rModule(verilog_indexert::idt::kindt, int end_token);
  void rImport();
  void rExtends();
  void rPorts();
  void rItem();
  void rBind();

  void rCell();
  void rDesign();
  void rInterconnect();
  void rModport();
  void rConstruct(); // always, initial, ...
  void rStatement();
  void rBegin();
  void rFor();
  void rForEach();
  void rForEver();
  void rFork();
  void rRepeat();
  void rWait();
  void rWhile();
  void rDisable();
  void rForce();
  void rRelease();
  void rReturn();
  void rIf();
  void rCase();
  void rCaseLabel();
  void rUniquePriority();
  void rParenExpression(); // (expression)
  void rDeclaration();     // var, reg, wire, input, typedef, defparam ...
  void rType();
  void rTypeOpt();
  void rStructUnion();
  void rEnum();
  void rDeclarators();
  void rTaskFunction();     // task ... endtask
  void rConstraint();       // constraint ID { ... }
  void rContinuousAssign(); // assign
  void rGenerate();         // generate ... endgenerate
  void rGenerateFor();
  void rGenerateIf();
  void rGenerateBegin();
  void rModuleInstance();
  void rLabeledItem();
  void rAssertAssumeCover();
  void rClocking();
  void rCoverGroup();
  void rProperty();
  void rSequence();
  void rSpecify();
  void skip_until(int token);

  struct tokent
  {
    int kind;
    std::string text;
    bool is_eof() const
    {
      return kind == 0; // EOF, flex magic number
    }
    bool is_identifier() const
    {
      return kind == TOK_NON_TYPE_IDENTIFIER || kind == TOK_TYPE_IDENTIFIER;
    }
    bool is_system_identifier() const
    {
      return kind == TOK_SYSIDENT;
    }
    bool operator==(int other) const
    {
      return kind == other;
    }
    bool operator!=(int other) const
    {
      return kind != other;
    }
  };

  static bool may_be_type(const tokent &);

  // consume a token, returned as rvalue
  tokent next_token();

  // lookahead, returned as reference
  const tokent &peek(std::size_t k = 1);

  // the token buffer
  std::deque<tokent> tokens;

  // get a token from the scanner
  static tokent fetch_token();

public:
  // used as scanner interface
  verilog_parsert verilog_parser;
};

#endif
