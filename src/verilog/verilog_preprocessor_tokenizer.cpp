/*******************************************************************\

Module: Verilog Preprocessor Tokenizer

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "verilog_preprocessor_tokenizer.h"

#include <util/invariant.h>

#include <algorithm>

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
    if(!token.is_ws_not_nl())
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
  else if(token.is_string_literal())
  {
    // string literals may span lines, using a line continuation
    _line_no += std::count(token.text.begin(), token.text.end(), '\n');
  }

  return token;
}

void verilog_preprocessor_tokenizert::get_token_from_stream()
{
  // Each tokenizer wraps its own reentrant flex scanner (its own state
  // and buffer), so a file and the `include files opened while reading
  // it can be tokenized independently.
  token.kind =
    static_cast<verilog_preprocessor_tokenizert::tokent::kindt>(scanner.lex());
  token.text = std::string(scanner.text(), scanner.leng());
}

std::vector<verilog_preprocessor_token_sourcet::tokent>
verilog_preprocessor_tokenize(const std::string &text)
{
  std::istringstream instream(text);
  verilog_preprocessor_tokenizert tokenizer(instream);
  std::vector<verilog_preprocessor_token_sourcet::tokent> result;
  while(!tokenizer.eof())
    result.push_back(tokenizer.next_token());
  return result;
}
