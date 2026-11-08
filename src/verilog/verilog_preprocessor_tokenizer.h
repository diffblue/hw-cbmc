/*******************************************************************\

Module: Verilog Preprocessor Tokenizer

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef VERILOG_PREPROCESSOR_TOKENIZER_H
#define VERILOG_PREPROCESSOR_TOKENIZER_H

#include "verilog_preprocessor_error.h"

#define FLEX_PREFIX yyverilog_preprocessor
#include "flex_interface.h"

#include <vector>

// returns true if the argument is space, tab, vertical tab,
// formfeed, carriage return, but not a newline
static bool verilog_is_ws_not_nl(int ch)
{
  // We don't use isspace, since that requires that the argument
  // is representable as an unsigned char.
  return ch == ' ' || ch == '\t' || ch == '\v' || ch == '\f' || ch == '\r';
}

/// Note that the set of tokens recognised by the Verilog preprocessor
/// differs from the set of tokens used by the main parser.

class verilog_preprocessor_token_sourcet
{
public:
  virtual ~verilog_preprocessor_token_sourcet() = default;

  class tokent
  {
  public:
    using kindt = enum {
      END_OF_FILE = 0, // defined by flex
      NONE = 256,
      IDENTIFIER,
      STRING_LITERAL
    };
    kindt kind = NONE;
    std::string text;
    bool is_eof() const
    {
      return kind == END_OF_FILE;
    }
    bool is_identifier() const
    {
      return kind == IDENTIFIER;
    }
    bool is_string_literal() const
    {
      return kind == STRING_LITERAL;
    }
    bool is_ws_not_nl() const
    {
      return ::verilog_is_ws_not_nl(static_cast<int>(kind));
    }
    bool is_ws() const
    {
      return ::verilog_is_ws_not_nl(static_cast<int>(kind)) ||
             static_cast<int>(kind) == '\n';
    }
    bool operator==(char ch) const
    {
      return static_cast<int>(kind) == ch;
    }
    bool operator!=(char ch) const
    {
      return static_cast<int>(kind) != ch;
    }
    friend std::ostream &operator<<(std::ostream &out, const tokent &t)
    {
      return out << t.text;
    }
    std::string string_literal_value() const;
  };

  // convenience helpers
  bool eof();
  void skip_ws();
  void skip_until_eol();

  // 1800-2017 22.5.1: While reading `define macro text, a one-line
  // comment ending in a backslash continues the macro text on the
  // next line.
  bool in_macro_text = false;

  // get the next token from the stream
  const tokent &next_token();

  // get the next token without consuming it
  const tokent &peek();

  std::size_t line_no() const
  {
    return _line_no;
  }

protected:
  std::size_t _line_no = 1;
  bool peeked = false;
  tokent token; // for peeking

  /// read a token from the input stream and store it in 'token'
  virtual void get_token_from_stream() = 0;
};

// The scanner is the flex-generated reentrant tokenizer wrapped by
// flex_interfacet (FLEX_CLASS_NAME). The subclass adds the
// preprocessor-specific in_macro_text flag, which the scanner reads via
// yyget_extra(). The flag itself lives on the token source (not the
// generic flex base).
class verilog_preprocessor_scannert : public FLEX_CLASS_NAME
{
public:
  verilog_preprocessor_scannert(std::istream &_in, const bool &_in_macro_text)
    : FLEX_CLASS_NAME(_in), in_macro_text(_in_macro_text)
  {
  }

  // see verilog_preprocessor_token_sourcet::in_macro_text
  const bool &in_macro_text;
};

class verilog_preprocessor_tokenizert
  : public verilog_preprocessor_token_sourcet
{
public:
  explicit verilog_preprocessor_tokenizert(std::istream &_in)
    : scanner(_in, in_macro_text)
  {
  }

protected:
  verilog_preprocessor_scannert scanner;
  void get_token_from_stream() override;
};

// tokenize a given string
std::vector<verilog_preprocessor_token_sourcet::tokent>
verilog_preprocessor_tokenize(const std::string &);

#endif // VERILOG_PREPROCESSOR_TOKENIZER_H
