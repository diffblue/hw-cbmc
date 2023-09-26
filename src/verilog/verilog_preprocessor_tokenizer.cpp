/*******************************************************************\

Module: Verilog Preprocessor Tokenizer

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "verilog_preprocessor_tokenizer.h"

#include <util/invariant.h>

void verilog_preprocessor_token_sourcet::skip_until_eol()
{
  while(true)
  {
    auto token = peek();
    if(token == '\n' || token.is_eof())
      break;
    next_token(); // eat
  }
}

void verilog_preprocessor_token_sourcet::skip_ws()
{
  while(true)
  {
    auto token = peek();
    if(token != ' ' && token != '\t')
      break;
    next_token(); // eat
  }
}

std::string
verilog_preprocessor_token_sourcet::tokent::string_literal_value() const
{
  PRECONDITION(kind == STRING_LITERAL);
  PRECONDITION(text.size() >= 2);
  std::string result;
  result.reserve(text.size());

  for(std::size_t i = 1; i < text.size() - 1; i++)
  {
    char ch = text[i];
    result += ch;
  }

  return result;
}

bool verilog_preprocessor_token_sourcet::eof()
{
  return peek().is_eof();
}

auto verilog_preprocessor_token_sourcet::peek() -> const tokent &
{
  if(peeked)
    return token;
  else
  {
    get_token_from_stream();
    peeked = true;
    return token;
  }
}

auto verilog_preprocessor_token_sourcet::next_token() -> const tokent &
{
  if(peeked)
    peeked = false;
  else
    get_token_from_stream();

  if(token == '\n')
    _line_no++;

  return token;
}

verilog_preprocessor_tokenizert::verilog_preprocessor_tokenizert(
  std::istream &_in)
  : in(_in)
{
}

std::size_t
verilog_preprocessor_tokenizert::yy_input(char *buffer, std::size_t max_size)
{
  std::size_t result = 0;
  while(result < max_size)
  {
    char ch;
    if(!in.get(ch))
      break; // eof
    buffer[result++] = ch;
    if(ch == '\n')
    {
      // We need to abort prematurely to enable
      // switching input streams on `include.
      break;
    }
  }
  return result;
}

int yyverilog_preprocessorlex();
verilog_preprocessor_tokenizert *verilog_preprocessor_tokenizer;

void verilog_preprocessor_tokenizert::get_token_from_stream()
{
  verilog_preprocessor_tokenizer = this;
  token.kind = static_cast<verilog_preprocessor_tokenizert::tokent::kindt>(
    yyverilog_preprocessorlex());
}
