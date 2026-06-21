/*******************************************************************\

Module: Flex Interface

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_FLEX_INTERFACE_H
#define CPROVER_FLEX_INTERFACE_H

#include <cstddef>
#include <iosfwd>
#include <utility>

// This is a C++ interface for a flex-generated tokenizer.
// Defining our own avoids the issue with the different versions
// of the FlexLexer.h, which needs to match the version of the
// flex binary.

class flex_interfacet
{
public:
  virtual ~flex_interfacet()
  {
    destroy();
  }

  // the return type is hard-wired by flex
  virtual int lex() = 0;

  // for calling yylex_init
  virtual void init()
  {
  }

  // for calling yylex_destroy
  virtual void destroy()
  {
  }

  // to be called by the YY_INPUT macro, as follows
  // #define YY_INPUT(buf, result, max_size)
  // { result = flex_interface.yy_input(buf, max_size); }
  std::size_t yy_input(char *buffer, std::size_t max_size);

  // yytext and yyleng
  using text_and_lengt = std::pair<char *, std::size_t>;
  virtual text_and_lengt text_and_leng() = 0;

  std::istream *in = nullptr;
};

#endif // CPROVER_FLEX_INTERFACE_H
