/*******************************************************************\

Module: SMV Parser

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SMV_PARSER_H
#define CPROVER_SMV_PARSER_H

#include <util/parser.h>

#include "smv_parse_tree.h"

int yysmvparse();

extern class smv_parsert *smv_parser_ptr;

class smv_parsert:public parsert
{
public:
  explicit smv_parsert(message_handlert &message_handler)
    : parsert(message_handler)
  {
    PRECONDITION(smv_parser_ptr == nullptr);
    smv_parser_ptr = this;
  }

  ~smv_parsert()
  {
    smv_parser_ptr = nullptr;
  }

  smv_parse_treet parse_tree;
  smv_parse_treet::modulet *module;

  bool parse() override;

  /// Set by the scanner when it encounters an error that
  /// the parser doesn't see, e.g., an unterminated comment.
  bool scanner_error = false;

  /// Returns the next token. Called by the generated parser.
  /// Only valid during parse().
  int lex();

  /// Returns the text of the most recently scanned token.
  /// Only valid during parse().
  const char *token_text() const;

protected:
  /// The tokenizer, which exists only during parse().
  class yysmvflext *scanner = nullptr;
};

#endif
