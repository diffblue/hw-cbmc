/*******************************************************************\

Module: Flex Interface

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_VERILOG_FLEX_INTERFACE_H
#define CPROVER_VERILOG_FLEX_INTERFACE_H

#include <cstddef>
#include <iosfwd>

// This is a C++ interface for a flex-generated tokenizer.
// Defining our own avoids the issue with the different versions
// of the FlexLexer.h, which needs to match the version of the
// flex binary.
// This encapsulates the entire state of the Flex lexer.

// Define FLEX_PREFIX to the flex "prefix=" / -P value when a prefix is
// used. The same prefix names both the C++ class (FLEX_PREFIX ## flext)
// and the generated flex functions (FLEX_PREFIX ## lex etc.), so it must
// also be passed to flex. FLEX_FN forms those prefixed function names
// directly: flex keeps the unprefixed spellings (yylex, ...) usable in
// the trailing user-code section only from 2.6.4 on, so forming the real
// names here lets flex_interface.inc build with older flex too (e.g. the
// 2.6.1 shipped by CentOS 8).
#ifdef FLEX_PREFIX
// Expand FLEX_PREFIX before pasting (## does not expand its operands).
#  define FLEX_PASTE(a, b) a##b
#  define FLEX_EXPAND(a, b) FLEX_PASTE(a, b)
#  define FLEX_CLASS_NAME FLEX_EXPAND(FLEX_PREFIX, flext)
#  define FLEX_FN(name) FLEX_EXPAND(FLEX_PREFIX, name)
#else
#  define FLEX_CLASS_NAME flext
#  define FLEX_FN(name) yy##name
#endif

class flex_interface_baset
{
public:
  /* for usage by the YY_INPUT macro, as follows:
  #define YY_INPUT(buf, result, max_size) \
    { result = static_cast<FLEX_CLASS_NAME *>( \
      yyget_extra(yyscanner))->yy_input(buf, max_size); }
  */
  std::size_t yy_input(char *buffer, std::size_t max_size);

protected:
  // input stream
  std::istream *in = nullptr;

  // Scanner state. We assume this can be cast to yyscan_t.
  void *state = nullptr;
};

class FLEX_CLASS_NAME : public flex_interface_baset
{
public:
  ~FLEX_CLASS_NAME()
  {
    destroy();
  }

  explicit FLEX_CLASS_NAME(std::istream &_in)
  {
    in = &_in;
    init_extra(this);
  }

  // This class owns the flex state, which can't be copied
  FLEX_CLASS_NAME(const FLEX_CLASS_NAME &) = delete;
  FLEX_CLASS_NAME &operator=(const FLEX_CLASS_NAME &) = delete;

  // the return type is hard-wired by flex
  int lex();

  // yytext
  char *text();

  // yyleng
  std::size_t leng() const;

  // yylineno
  int lineno() const;
  void lineno(int);

  // helper to cast yyget_extra's return value
  static FLEX_CLASS_NAME &from_extra(void *extra)
  {
    return *static_cast<FLEX_CLASS_NAME *>(extra);
  }

protected:
  // for calling yylex_init_extra
  void init_extra(void *);

  // for calling yylex_destroy
  void destroy();
};

#endif // CPROVER_VERILOG_FLEX_INTERFACE_H
