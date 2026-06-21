%option nounput
%option noinput

%{
#include <util/pragma_wdeprecated_register.def>
#include <util/pragma_wsign_compare.def>
#include <util/pragma_wnull_conversion.def>

#ifdef _WIN32
#define YY_NO_UNISTD_H
static int isatty(int) { return 0; }
#endif

#include "verilog_preprocessor_tokenizer.h"

extern flex_interfacet *verilog_preprocessor_flex;
using tokent = verilog_preprocessor_tokenizert::tokent;

#define YY_INPUT(buf, result, max_size) \
  { result = verilog_preprocessor_flex->yy_input(buf, max_size); }
%}

%s SLCOMMENT
%s MLCOMMENT
%s STRING

Identifier	[a-zA-Z_][0-9a-zA-Z_$]*
String		\"(\\.|[^"\\])*\"

%%

<INITIAL>"//"		{ BEGIN SLCOMMENT; /* single-line comment */ }
<INITIAL>"/*"           { BEGIN MLCOMMENT; /* multi-line comment */ }
<INITIAL>{String}	{ return tokent::STRING_LITERAL; }
<INITIAL>{Identifier}	{ return tokent::IDENTIFIER; }
<INITIAL>.|\n		{ return yytext[0]; /* anything else */ }
<SLCOMMENT>\n		{ BEGIN INITIAL; return '\n'; }
<SLCOMMENT>.		{ /* just eat up */ }
<SLCOMMENT><<EOF>>      { /* we allow that */ BEGIN INITIAL; }
<MLCOMMENT>\n		{ return '\n'; }
<MLCOMMENT>"*/"         { BEGIN INITIAL; /* comment done */ }
<MLCOMMENT>.		{ /* just eat up */ }
<MLCOMMENT><<EOF>>      { throw verilog_preprocessor_errort() << "EOF inside a comment"; }

%%

int yywrap() { return 1; }

void verilog_preprocessor_flext::init()
{
  YY_FLUSH_BUFFER;
  BEGIN INITIAL;
}

int verilog_preprocessor_flext::lex()
{
  return yylex();
}

verilog_preprocessor_flext::text_and_lengt
verilog_preprocessor_flext::text_and_leng()
{
  return {yytext, yyleng};
}
