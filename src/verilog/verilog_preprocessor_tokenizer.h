/*******************************************************************\

Module: Verilog Preprocessor Tokenizer

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef VERILOG_PREPROCESSOR_TOKENIZER_H
#define VERILOG_PREPROCESSOR_TOKENIZER_H

#include "verilog_preprocessor_error.h"

#include <vector>

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
    bool operator==(char ch) const
    {
      return static_cast<char>(kind) == ch;
    }
    bool operator!=(char ch) const
    {
      return static_cast<char>(kind) != ch;
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

class verilog_preprocessor_tokenizert
  : public verilog_preprocessor_token_sourcet
{
public:
  explicit verilog_preprocessor_tokenizert(std::istream &_in);

  // for flex
  std::size_t yy_input(char *buffer, std::size_t max_size);
  void text(const char *buffer, std::size_t len)
  {
    token.text = std::string(buffer, len);
  }

  void text(char ch)
  {
    token.text = std::string(1, ch);
  }

protected:
  std::istream &in;
  void get_token_from_stream() override;
};

// tokenize a given string
std::vector<verilog_preprocessor_token_sourcet::tokent>
verilog_preprocessor_tokenize(const std::string &);

#endif // VERILOG_PREPROCESSOR_TOKENIZER_H
