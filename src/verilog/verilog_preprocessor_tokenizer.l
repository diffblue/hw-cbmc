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

extern verilog_preprocessor_tokenizert *verilog_preprocessor_tokenizer;
using tokent = verilog_preprocessor_tokenizert::tokent;

#define TOKENIZER (*verilog_preprocessor_tokenizer)

#define YY_INPUT(buf, result, max_size) \
  { result = TOKENIZER.yy_input(buf, max_size); }
%}

%s SLCOMMENT
%s MLCOMMENT
%s STRING

Identifier	[a-zA-Z_][0-9a-zA-Z_$]*
String		\"(\\.|[^"\\])*\"

%%

<INITIAL>"//"		{ BEGIN SLCOMMENT; /* single-line comment */ }
<INITIAL>"/*"           { BEGIN MLCOMMENT; /* multi-line comment */ }
<INITIAL>{String}	{ TOKENIZER.text(yytext, yyleng); return tokent::STRING_LITERAL; }
<INITIAL>{Identifier}	{ TOKENIZER.text(yytext, yyleng); return tokent::IDENTIFIER; }
<INITIAL>.|\n		{ TOKENIZER.text(yytext[0]); return yytext[0]; /* anything else */ }
<SLCOMMENT>\n		{ BEGIN INITIAL; TOKENIZER.text('\n'); return '\n'; }
<SLCOMMENT>.		{ /* just eat up */ }
<SLCOMMENT><<EOF>>      { throw verilog_preprocessor_errort() << "EOF inside a comment"; }
<MLCOMMENT>\n		{ TOKENIZER.text('\n'); return '\n'; }
<MLCOMMENT>"*/"         { BEGIN INITIAL; /* comment done */ }
<MLCOMMENT>.		{ /* just eat up */ }
<MLCOMMENT><<EOF>>      { throw verilog_preprocessor_errort() << "EOF inside a comment"; }

%%

int yywrap() { return 1; }

void verilog_preprocessor_tokenizer_init()
{
  YY_FLUSH_BUFFER;
  BEGIN INITIAL;
}
