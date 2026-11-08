%option nounput
%option noinput
%option reentrant
%option noyywrap

%{
#include <util/pragma_wdeprecated_register.def>
#include <util/pragma_wsign_compare.def>
#include <util/pragma_wnull_conversion.def>

#ifdef _WIN32
#define YY_NO_UNISTD_H
static int isatty(int) { return 0; }
#endif

#include "verilog_preprocessor_tokenizer.h"

using tokent = verilog_preprocessor_tokenizert::tokent;

// The scanner is reentrant; its "extra" data is the flex_interfacet
// wrapper (a verilog_preprocessor_scannert), reached via yyget_extra.
#define YY_INPUT(buf, result, max_size)                          \
  {                                                              \
    result = FLEX_CLASS_NAME::from_extra(yyget_extra(yyscanner)) \
               .yy_input(buf, max_size);                         \
  }
%}

%s SLCOMMENT
%s MLCOMMENT
%s STRING

Identifier	[a-zA-Z_][0-9a-zA-Z_$]*
String		\"(\\(.|\n)|[^"\\])*\"

%%

<INITIAL>"//"		{ BEGIN SLCOMMENT; /* single-line comment */ }
<INITIAL>"/*"           { BEGIN MLCOMMENT; /* multi-line comment */ }
<INITIAL>{String}	{ return tokent::STRING_LITERAL; }
<INITIAL>{Identifier}	{ return tokent::IDENTIFIER; }
<INITIAL>.|\n		{ return yytext[0]; /* anything else */ }
<SLCOMMENT>\n		{ BEGIN INITIAL; return '\n'; }
<SLCOMMENT>\\\n		{
			  /* 1800-2017 22.5.1: a one-line comment ending in a
			     backslash continues a `define on the next line */
			  if(static_cast<const verilog_preprocessor_scannert &>(
			       FLEX_CLASS_NAME::from_extra(yyget_extra(yyscanner))).in_macro_text)
			  {
			    yyless(1); /* return the \n to the input */
			    return '\\';
			  }
			  else
			  {
			    BEGIN INITIAL;
			    yyless(1); /* rescan the \n as a newline token */
			  }
			}
<SLCOMMENT>.		{ /* just eat up */ }
<SLCOMMENT><<EOF>>      { /* we allow that */ BEGIN INITIAL; }
<MLCOMMENT>\n		{ return '\n'; }
<MLCOMMENT>"*/"         { BEGIN INITIAL; /* comment done */ }
<MLCOMMENT>.		{ /* just eat up */ }
<MLCOMMENT><<EOF>>      { throw verilog_preprocessor_errort() << "EOF inside a comment"; }

%%

#include "flex_interface.inc"
