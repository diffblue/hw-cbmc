%option nounput
%option noinput

%{

#ifdef _WIN32
#define YY_NO_UNISTD_H
static int isatty(int) { return 0; }
#endif

#include <cassert>
#include <cstdlib>
#include <cstring>

#include <util/expr.h>

#define PARSER verilog_parser
#define YYSTYPE unsigned

#include "verilog_parser.h"
#include "verilog_y.tab.h"

int yyverilogerror(const char *error);

static void line_directive()
{
  char *tptr=yytext;

  // skip directive
  while(*tptr!=' ' && *tptr!='\t' && *tptr!=0) tptr++;

  // skip whitespace
  while(*tptr==' ' || *tptr=='\t') tptr++;

  PARSER.set_line_no(atoi(tptr)-1);

  // skip number

  while(isdigit(*tptr)) tptr++;

  // skip whitespace
  while(*tptr==' ' || *tptr=='\t') tptr++;

  if(*tptr=='"') // filename?
  {
    tptr++;

    std::string filename;
    while(*tptr!=0 && *tptr!='"')
      filename+=*(tptr++);

    PARSER.set_file(filename);
  }
}

static void preprocessor()
{

}

#define IDENTIFIER { newstack(yyveriloglval); stack(yyveriloglval).id(yytext); return TOK_CHARSTR; }
#define SYSTEM_VERILOG_KEYWORD(x) \
  { if(PARSER.mode==verilog_parsert::SYSTEM_VERILOG) \
      return x; \
    else \
      IDENTIFIER; \
  }
#define VIS_VERILOG_KEYWORD(x) \
  { if(PARSER.mode==verilog_parsert::SYSTEM_VERILOG || \
       PARSER.mode==verilog_parsert::VIS_VERILOG) \
      return x; \
    else \
      IDENTIFIER; \
  }
%}

%pointer

%x GRAMMAR
%s COMMENT
%s STRING

NL		[\n]
WS		[ \t\r\b]
WSNL		[{WS}{NL}]
Digit		[0-9]
DigitU		[0-9_]
Letter		[a-zA-Z]
LetterU		[a-zA-Z_]
WordNum		[0-9a-zA-Z]
WordNumUD	[0-9a-zA-Z_$]
WSs		{WS}+
WSst		{WS}*
Number		{Digit}{DigitU}*
Word		{LetterU}{WordNumUD}*
EscapedWord     "\\"[^\n \t\r]+
Binary		({Number})?{WSst}'{WSst}[sS]?[bB]{WSst}[01xXzZ?]([01xXzZ?_])*
Octal           ({Number})?{WSst}'{WSst}[sS]?[oO]{WSst}[0-7xXzZ?]([0-7xXzZ?_])*
Decimal		({Number})?{WSst}'{WSst}[sS]?[dD]{WSst}{Number}
Hexdecimal	({Number})?{WSst}'{WSst}[sS]?[hH]{WSst}[0-9a-fA-FxXzZ?]([0-9a-fA-FxXzZ?_])*
Real		{Number}\.{Number}
RealExp		{Number}(\.{Number})?[eE][+-]?{Number}
Comment		"//"[^\n]*{NL}

%{
void verilog_scanner_init()
 {
  YY_FLUSH_BUFFER;
  BEGIN 0; // INITIAL
 }
%}

%%

<INITIAL>.|\n	{ BEGIN GRAMMAR;
		  yyless(0);		/* start again with this character */
		  //yy_current_buffer->yy_at_bol = 1; /* at beginning of line */
		  switch(PARSER.grammar)
		   {
                   case verilog_parsert::EXPRESSION: return TOK_PARSE_EXPRESSION;
                   case verilog_parsert::TYPE: return TOK_PARSE_TYPE;
                   case verilog_parsert::LANGUAGE: return TOK_PARSE_LANGUAGE;
		   default: assert(0);
		   }
		}

<GRAMMAR>{NL}           { continue; }
<GRAMMAR>{WSs}		{ continue; }
<GRAMMAR>{Comment}      { continue; }
<GRAMMAR>"/*"           { BEGIN COMMENT; continue; }
<COMMENT>{NL}           { continue; }
<COMMENT>.              { continue; }
<COMMENT>"*/"           { BEGIN GRAMMAR; continue; }

<GRAMMAR>"\""	{ BEGIN(STRING);	/* begin string literal state */
		  newstack(yyveriloglval);
                  verilog_parser.string_literal.clear();
		}

<STRING>{
   "\""		{ BEGIN(GRAMMAR);	/* end string state, back GRAMMAR */
                  stack(yyveriloglval).id(verilog_parser.string_literal);
		  return TOK_QSTRING;
		}

   <<EOF>>	{ yyverilogerror("Unterminated string constant");
		  return TOK_SCANNER_ERROR;
		}

   "\\n"	{ verilog_parser.string_literal += '\n'; }	/* NL (0x0a) */
   "\\t"	{ verilog_parser.string_literal += '\t'; }	/* HT (0x09) */
   "\\".	{ verilog_parser.string_literal += yytext[1]; } /* ignore the backslash */
   [^\\\"\n]*	{ verilog_parser.string_literal += &yytext[0]; } /* standard stuff */

   \n		{ yyverilogerror("Unterminated string constant");
		  return TOK_SCANNER_ERROR;
		}
}

	/*
	 * Symbols.
	 */

	/* Generic. */

<GRAMMAR>"(*"           { return TOK_PARENASTERIC; }
<GRAMMAR>"*)"           { return TOK_ASTERICPAREN; }

	/* Unary. */

<GRAMMAR>"+"            { return TOK_PLUS; }
<GRAMMAR>"-"            { return TOK_MINUS; }
<GRAMMAR>"!"            { return TOK_EXCLAM; }
<GRAMMAR>"~"            { return TOK_TILDE; }
<GRAMMAR>"&"            { return TOK_AMPER; }
<GRAMMAR>"~&"           { return TOK_TILDEAMPER; }
<GRAMMAR>"|"            { return TOK_VERTBAR; }
<GRAMMAR>"~|"           { return TOK_TILDEVERTBAR; }
<GRAMMAR>"^"            { return TOK_CARET; }
<GRAMMAR>"~^"           { return TOK_TILDECARET; }
<GRAMMAR>"^~"           { return TOK_CARETTILDE; }
<GRAMMAR>"->"           { return TOK_MINUSGREATER; }

	/* Binary. */

<GRAMMAR>"*"            { return TOK_ASTERIC; }
<GRAMMAR>"/"            { return TOK_SLASH; }
<GRAMMAR>"%"            { return TOK_PERCENT; }
<GRAMMAR>"=="           { return TOK_EQUALEQUAL; }
<GRAMMAR>"!="           { return TOK_EXCLAMEQUAL; }
<GRAMMAR>"==="          { return TOK_EQUALEQUALEQUAL; }
<GRAMMAR>"!=="          { return TOK_EXCLAMEQUALEQUAL; }
<GRAMMAR>"&&"           { return TOK_AMPERAMPER; }
<GRAMMAR>"||"           { return TOK_VERTBARVERTBAR; }
<GRAMMAR>"**"           { return TOK_ASTERICASTERIC; }
<GRAMMAR>"<"            { return TOK_LESS; }
<GRAMMAR>"<="           { return TOK_LESSEQUAL; }
<GRAMMAR>">"            { return TOK_GREATER; }
<GRAMMAR>">="           { return TOK_GREATEREQUAL; }
<GRAMMAR>">>"           { return TOK_GREATERGREATER; }
<GRAMMAR>">>>"          { return TOK_GREATERGREATERGREATER; }
<GRAMMAR>"<<"           { return TOK_LESSLESS; }
<GRAMMAR>"<<<"          { return TOK_LESSLESSLESS; }

	/* Trinary */

<GRAMMAR>"?"		{ return TOK_QUESTION; }
<GRAMMAR>":"		{ return TOK_COLON; }

        /* System Verilog */
<GRAMMAR>"|->"          { if(PARSER.mode==verilog_parsert::SYSTEM_VERILOG)
                            return TOK_VERTBARMINUSGREATER;
                          else
                            yyverilogerror("|-> is a System Verilog operator");
                        }
<GRAMMAR>"|=>"          { if(PARSER.mode==verilog_parsert::SYSTEM_VERILOG)
                            return TOK_VERTBAREQUALGREATER;
                          else
                            yyverilogerror("|=> is a System Verilog operator");
                        }
<GRAMMAR>"++"           { if(PARSER.mode==verilog_parsert::SYSTEM_VERILOG)
                            return TOK_PLUSPLUS;
                          else
                            yyverilogerror("++ is a System Verilog operator");
                        }
<GRAMMAR>"--"           { if(PARSER.mode==verilog_parsert::SYSTEM_VERILOG)
                            return TOK_MINUSMINUS;
                          else
                            yyverilogerror("-- is a System Verilog operator");
                        }
<GRAMMAR>"+="           { if(PARSER.mode==verilog_parsert::SYSTEM_VERILOG)
                            return TOK_PLUSEQUAL;
                          else
                            yyverilogerror("+= is a System Verilog operator");
                        }
<GRAMMAR>"+:"           { if(PARSER.mode==verilog_parsert::SYSTEM_VERILOG)
                            return TOK_PLUSCOLON;
                          else
                            yyverilogerror("+: is a System Verilog operator");
                        }
<GRAMMAR>"-:"           { if(PARSER.mode==verilog_parsert::SYSTEM_VERILOG)
                            return TOK_MINUSCOLON;
                          else
                            yyverilogerror("-: is a System Verilog operator");
                        }
<GRAMMAR>"-="           { if(PARSER.mode==verilog_parsert::SYSTEM_VERILOG)
                            return TOK_MINUSEQUAL;
                          else
                            yyverilogerror("-= is a System Verilog operator");
                        }
<GRAMMAR>"*="           { if(PARSER.mode==verilog_parsert::SYSTEM_VERILOG)
                            return TOK_ASTERICEQUAL;
                          else
                            yyverilogerror("*= is a System Verilog operator");
                        }
<GRAMMAR>"/="           { if(PARSER.mode==verilog_parsert::SYSTEM_VERILOG)
                            return TOK_SLASHEQUAL;
                          else
                            yyverilogerror("+= is a System Verilog operator");
                        }
<GRAMMAR>"%="           { if(PARSER.mode==verilog_parsert::SYSTEM_VERILOG)
                            return TOK_PERCENTEQUAL;
                          else
                            yyverilogerror("%= is a System Verilog operator");
                        }
<GRAMMAR>"&="           { if(PARSER.mode==verilog_parsert::SYSTEM_VERILOG)
                            return TOK_AMPEREQUAL;
                          else
                            yyverilogerror("&= is a System Verilog operator");
                        }
<GRAMMAR>"^="           { if(PARSER.mode==verilog_parsert::SYSTEM_VERILOG)
                            return TOK_CARETEQUAL;
                          else
                            yyverilogerror("^= is a System Verilog operator");
                        }
<GRAMMAR>"|="           { if(PARSER.mode==verilog_parsert::SYSTEM_VERILOG)
                            return TOK_VERTBAREQUAL;
                          else
                            yyverilogerror("|= is a System Verilog operator");
                        }
<GRAMMAR>"<<="          { if(PARSER.mode==verilog_parsert::SYSTEM_VERILOG)
                            return TOK_LESSLESSEQUAL;
                          else
                            yyverilogerror("<<= is a System Verilog operator");
                        }
<GRAMMAR>">>="          { if(PARSER.mode==verilog_parsert::SYSTEM_VERILOG)
                            return TOK_GREATERGREATEREQUAL;
                          else
                            yyverilogerror(">>= is a System Verilog operator");
                        }
<GRAMMAR>"<<<="         { if(PARSER.mode==verilog_parsert::SYSTEM_VERILOG)
                            return TOK_LESSLESSLESSEQUAL;
                          else
                            yyverilogerror("<<<= is a System Verilog operator");
                        }
<GRAMMAR>">>>="         { if(PARSER.mode==verilog_parsert::SYSTEM_VERILOG)
                            return TOK_GREATERGREATERGREATEREQUAL;
                          else
                            yyverilogerror(">>>= is a System Verilog operator");
                        }
<GRAMMAR>"##"           { if(PARSER.mode==verilog_parsert::SYSTEM_VERILOG)
                            return TOK_HASHHASH;
                          else
                            yyverilogerror("## is a System Verilog operator");
                        }

        /* Verilog Keywords */

<GRAMMAR>always         { return TOK_ALWAYS; }
<GRAMMAR>and            { return TOK_AND; }
<GRAMMAR>assign         { return TOK_ASSIGN; }
<GRAMMAR>automatic      { return TOK_AUTOMATIC; }
<GRAMMAR>begin          { return TOK_BEGIN; }
<GRAMMAR>buf            { return TOK_BUF; }
<GRAMMAR>bufif0         { return TOK_BUFIF0; }
<GRAMMAR>bufif1         { return TOK_BUFIF1; }
<GRAMMAR>case           { return TOK_CASE; }
<GRAMMAR>casex          { return TOK_CASEX; }
<GRAMMAR>casez          { return TOK_CASEZ; }
<GRAMMAR>cmos           { return TOK_CMOS; }
<GRAMMAR>deassign       { return TOK_DEASSIGN; }
<GRAMMAR>default        { return TOK_DEFAULT; }
<GRAMMAR>defparam       { return TOK_DEFPARAM; }
<GRAMMAR>disable        { return TOK_DISABLE; }
<GRAMMAR>edge           { return TOK_EDGE; }
<GRAMMAR>else           { return TOK_ELSE; }
<GRAMMAR>end            { return TOK_END; }
<GRAMMAR>endcase        { return TOK_ENDCASE; }
<GRAMMAR>endfunction    { return TOK_ENDFUNCTION; }
<GRAMMAR>endgenerate    { return TOK_ENDGENERATE; }
<GRAMMAR>endmodule      { return TOK_ENDMODULE; }
<GRAMMAR>endprimitive   { return TOK_ENDPRIMITIVE; }
<GRAMMAR>endspecify     { return TOK_ENDSPECIFY; }
<GRAMMAR>endtable       { return TOK_ENDTABLE; }
<GRAMMAR>endtask        { return TOK_ENDTASK; }
<GRAMMAR>event          { return TOK_EVENT; }
<GRAMMAR>for            { return TOK_FOR; }
<GRAMMAR>force          { return TOK_FORCE; }
<GRAMMAR>forever        { return TOK_FOREVER; }
<GRAMMAR>fork           { return TOK_FORK; }
<GRAMMAR>function       { return TOK_FUNCTION; }
<GRAMMAR>generate       { return TOK_GENERATE; }
<GRAMMAR>genvar         { return TOK_GENVAR; }
<GRAMMAR>highz0         { return TOK_HIGHZ0; }
<GRAMMAR>highz1         { return TOK_HIGHZ1; }
<GRAMMAR>if             { return TOK_IF; }
<GRAMMAR>ifnone         { return TOK_IFNONE; }
<GRAMMAR>initial        { return TOK_INITIAL; }
<GRAMMAR>inout          { return TOK_INOUT; }
<GRAMMAR>input          { return TOK_INPUT; }
<GRAMMAR>integer        { return TOK_INTEGER; }
<GRAMMAR>join           { return TOK_JOIN; }
<GRAMMAR>large          { return TOK_LARGE; }
<GRAMMAR>localparam	{ return TOK_LOCALPARAM; }
<GRAMMAR>macromodule    { return TOK_MACROMODULE; }
<GRAMMAR>medium         { return TOK_MEDIUM; }
<GRAMMAR>module         { return TOK_MODULE; }
<GRAMMAR>nand           { return TOK_NAND; }
<GRAMMAR>negedge        { return TOK_NEGEDGE; }
<GRAMMAR>nmos           { return TOK_NMOS; }
<GRAMMAR>nor            { return TOK_NOR; }
<GRAMMAR>not            { return TOK_NOT; }
<GRAMMAR>notif0         { return TOK_NOTIF0; }
<GRAMMAR>notif1         { return TOK_NOTIF1; }
<GRAMMAR>or             { return TOK_OR; }
<GRAMMAR>output         { return TOK_OUTPUT; }
<GRAMMAR>parameter      { return TOK_PARAMETER; }
<GRAMMAR>pmos           { return TOK_PMOS; }
<GRAMMAR>posedge        { return TOK_POSEDGE; }
<GRAMMAR>primitive      { return TOK_PRIMITIVE; }
<GRAMMAR>pull0          { return TOK_PULL0; }
<GRAMMAR>pull1          { return TOK_PULL1; }
<GRAMMAR>pulldown       { return TOK_PULLDOWN; }
<GRAMMAR>pullup         { return TOK_PULLUP; }
<GRAMMAR>rcmos          { return TOK_RCMOS; }
<GRAMMAR>real           { return TOK_REAL; }
<GRAMMAR>realtime       { return TOK_REALTIME; }
<GRAMMAR>reg            { return TOK_REG; }
<GRAMMAR>release        { return TOK_RELEASE; }
<GRAMMAR>repeat         { return TOK_REPEAT; }
<GRAMMAR>rnmos          { return TOK_RNMOS; }
<GRAMMAR>rpmos          { return TOK_RPMOS; }
<GRAMMAR>rtran          { return TOK_RTRAN; }
<GRAMMAR>rtranif0       { return TOK_RTRANIF0; }
<GRAMMAR>rtranif1       { return TOK_RTRANIF1; }
<GRAMMAR>scalared       { return TOK_SCALARED; }
<GRAMMAR>signed		{ return TOK_SIGNED; }
<GRAMMAR>small          { return TOK_SMALL; }
<GRAMMAR>specify        { return TOK_SPECIFY; }
<GRAMMAR>specparam      { return TOK_SPECPARAM; }
<GRAMMAR>strong0        { return TOK_STRONG0; }
<GRAMMAR>strong1        { return TOK_STRONG1; }
<GRAMMAR>supply0        { return TOK_SUPPLY0; }
<GRAMMAR>supply1        { return TOK_SUPPLY1; }
<GRAMMAR>table          { return TOK_TABLE; }
<GRAMMAR>task           { return TOK_TASK; }
<GRAMMAR>time           { return TOK_TIME; }
<GRAMMAR>tran           { return TOK_TRAN; }
<GRAMMAR>tranif0        { return TOK_TRANIF0; }
<GRAMMAR>tranif1        { return TOK_TRANIF1; }
<GRAMMAR>tri            { return TOK_TRI; }
<GRAMMAR>tri0           { return TOK_TRI0; }
<GRAMMAR>tri1           { return TOK_TRI1; }
<GRAMMAR>triand         { return TOK_TRIAND; }
<GRAMMAR>trior          { return TOK_TRIOR; }
<GRAMMAR>trireg         { return TOK_TRIREG; }
<GRAMMAR>vectored       { return TOK_VECTORED; }
<GRAMMAR>wait           { return TOK_WAIT; }
<GRAMMAR>wand           { return TOK_WAND; }
<GRAMMAR>weak0          { return TOK_WEAK0; }
<GRAMMAR>weak1          { return TOK_WEAK1; }
<GRAMMAR>wor            { return TOK_WOR; }
<GRAMMAR>while          { return TOK_WHILE; }
<GRAMMAR>wire           { return TOK_WIRE; }
<GRAMMAR>xnor           { return TOK_XNOR; }
<GRAMMAR>xor            { return TOK_XOR; }
<GRAMMAR>$setup         { return TOK_SETUP; }
<GRAMMAR>$hold          { return TOK_HOLD; }
<GRAMMAR>$recovery      { return TOK_RECOVERY; }
<GRAMMAR>$removal       { return TOK_REMOVAL; }
<GRAMMAR>$width         { return TOK_WIDTH; }
<GRAMMAR>$skew          { return TOK_SKEW; }

  /* System Verilog Keywords */
<GRAMMAR>accept_on	{ SYSTEM_VERILOG_KEYWORD(TOK_ACCEPT_ON); }
<GRAMMAR>alias		{ SYSTEM_VERILOG_KEYWORD(TOK_ALIAS); }
<GRAMMAR>always_comb	{ SYSTEM_VERILOG_KEYWORD(TOK_ALWAYS_COMB); }
<GRAMMAR>always_ff	{ SYSTEM_VERILOG_KEYWORD(TOK_ALWAYS_FF); }
<GRAMMAR>always_latch	{ SYSTEM_VERILOG_KEYWORD(TOK_ALWAYS_LATCH); }
<GRAMMAR>assert		{ VIS_VERILOG_KEYWORD(TOK_ASSERT); }
<GRAMMAR>assume		{ VIS_VERILOG_KEYWORD(TOK_ASSUME); }
<GRAMMAR>before		{ SYSTEM_VERILOG_KEYWORD(TOK_BEFORE); }
<GRAMMAR>bind		{ SYSTEM_VERILOG_KEYWORD(TOK_BIND); }
<GRAMMAR>bins		{ SYSTEM_VERILOG_KEYWORD(TOK_BINS); }
<GRAMMAR>binsof		{ SYSTEM_VERILOG_KEYWORD(TOK_BINSOF); }
<GRAMMAR>bit		{ SYSTEM_VERILOG_KEYWORD(TOK_BIT); }
<GRAMMAR>break		{ SYSTEM_VERILOG_KEYWORD(TOK_BREAK); }
<GRAMMAR>byte		{ SYSTEM_VERILOG_KEYWORD(TOK_BYTE); }
<GRAMMAR>chandle	{ SYSTEM_VERILOG_KEYWORD(TOK_CHANDLE); }
<GRAMMAR>checker	{ SYSTEM_VERILOG_KEYWORD(TOK_CHECKER); }
<GRAMMAR>class		{ SYSTEM_VERILOG_KEYWORD(TOK_CLASS); }
<GRAMMAR>clocking	{ SYSTEM_VERILOG_KEYWORD(TOK_CLOCKING); }
<GRAMMAR>const		{ SYSTEM_VERILOG_KEYWORD(TOK_CONST); }
<GRAMMAR>constraint	{ SYSTEM_VERILOG_KEYWORD(TOK_CONSTRAINT); }
<GRAMMAR>context	{ SYSTEM_VERILOG_KEYWORD(TOK_CONTEXT); }
<GRAMMAR>continue	{ SYSTEM_VERILOG_KEYWORD(TOK_CONTINUE); }
<GRAMMAR>cover		{ SYSTEM_VERILOG_KEYWORD(TOK_COVER); }
<GRAMMAR>covergroup	{ SYSTEM_VERILOG_KEYWORD(TOK_COVERGROUP); }
<GRAMMAR>coverpoint	{ SYSTEM_VERILOG_KEYWORD(TOK_COVERPOINT); }
<GRAMMAR>cross		{ SYSTEM_VERILOG_KEYWORD(TOK_CROSS); }
<GRAMMAR>dist		{ SYSTEM_VERILOG_KEYWORD(TOK_DIST); }
<GRAMMAR>do		{ SYSTEM_VERILOG_KEYWORD(TOK_DO); }
<GRAMMAR>endclass	{ SYSTEM_VERILOG_KEYWORD(TOK_ENDCLASS); }
<GRAMMAR>endclocking	{ SYSTEM_VERILOG_KEYWORD(TOK_ENDCLOCKING); }
<GRAMMAR>endgroup	{ SYSTEM_VERILOG_KEYWORD(TOK_ENDGROUP); }
<GRAMMAR>endinterface	{ SYSTEM_VERILOG_KEYWORD(TOK_ENDINTERFACE); }
<GRAMMAR>endpackage	{ SYSTEM_VERILOG_KEYWORD(TOK_ENDPACKAGE); }
<GRAMMAR>endprogram	{ SYSTEM_VERILOG_KEYWORD(TOK_ENDPROGRAM); }
<GRAMMAR>endproperty	{ SYSTEM_VERILOG_KEYWORD(TOK_ENDPROPERTY); }
<GRAMMAR>endsequence	{ SYSTEM_VERILOG_KEYWORD(TOK_ENDSEQUENCE); }
<GRAMMAR>enum		{ VIS_VERILOG_KEYWORD(TOK_ENUM); }
<GRAMMAR>eventually     { SYSTEM_VERILOG_KEYWORD(TOK_EVENTUALLY); }
<GRAMMAR>expect		{ SYSTEM_VERILOG_KEYWORD(TOK_EXPECT); }
<GRAMMAR>export		{ SYSTEM_VERILOG_KEYWORD(TOK_EXPORT); }
<GRAMMAR>extends	{ SYSTEM_VERILOG_KEYWORD(TOK_EXTENDS); }
<GRAMMAR>extern		{ SYSTEM_VERILOG_KEYWORD(TOK_EXTERN); }
<GRAMMAR>final		{ SYSTEM_VERILOG_KEYWORD(TOK_FINAL); }
<GRAMMAR>first_match	{ SYSTEM_VERILOG_KEYWORD(TOK_FIRST_MATCH); }
<GRAMMAR>foreach	{ SYSTEM_VERILOG_KEYWORD(TOK_FOREACH); }
<GRAMMAR>iff		{ SYSTEM_VERILOG_KEYWORD(TOK_IFF); }
<GRAMMAR>ignore_bins	{ SYSTEM_VERILOG_KEYWORD(TOK_IGNORE_BINS); }
<GRAMMAR>illegal_bins	{ SYSTEM_VERILOG_KEYWORD(TOK_ILLEGAL_BINS); }
<GRAMMAR>import		{ SYSTEM_VERILOG_KEYWORD(TOK_IMPORT); }
<GRAMMAR>inside		{ SYSTEM_VERILOG_KEYWORD(TOK_INSIDE); }
<GRAMMAR>int		{ SYSTEM_VERILOG_KEYWORD(TOK_INT); }
<GRAMMAR>interface	{ SYSTEM_VERILOG_KEYWORD(TOK_INTERFACE); }
<GRAMMAR>intersect	{ SYSTEM_VERILOG_KEYWORD(TOK_INTERSECT); }
<GRAMMAR>join_any	{ SYSTEM_VERILOG_KEYWORD(TOK_JOIN_ANY); }
<GRAMMAR>join_none	{ SYSTEM_VERILOG_KEYWORD(TOK_JOIN_NONE); }
<GRAMMAR>local		{ SYSTEM_VERILOG_KEYWORD(TOK_LOCAL); }
<GRAMMAR>logic		{ SYSTEM_VERILOG_KEYWORD(TOK_LOGIC); }
<GRAMMAR>longint	{ SYSTEM_VERILOG_KEYWORD(TOK_LONGINT); }
<GRAMMAR>matches	{ SYSTEM_VERILOG_KEYWORD(TOK_MATCHES); }
<GRAMMAR>modport	{ SYSTEM_VERILOG_KEYWORD(TOK_MODPORT); }
<GRAMMAR>new		{ SYSTEM_VERILOG_KEYWORD(TOK_NEW); }
<GRAMMAR>nexttime	{ SYSTEM_VERILOG_KEYWORD(TOK_NEXTTIME); }
<GRAMMAR>null		{ SYSTEM_VERILOG_KEYWORD(TOK_NULL); }
<GRAMMAR>package	{ SYSTEM_VERILOG_KEYWORD(TOK_PACKAGE); }
<GRAMMAR>packed		{ SYSTEM_VERILOG_KEYWORD(TOK_PACKED); }
<GRAMMAR>priority	{ SYSTEM_VERILOG_KEYWORD(TOK_PRIORITY); }
<GRAMMAR>program	{ SYSTEM_VERILOG_KEYWORD(TOK_PROGRAM); }
<GRAMMAR>property	{ SYSTEM_VERILOG_KEYWORD(TOK_PROPERTY); }
<GRAMMAR>protected	{ SYSTEM_VERILOG_KEYWORD(TOK_PROTECTED); }
<GRAMMAR>pure		{ SYSTEM_VERILOG_KEYWORD(TOK_PURE); }
<GRAMMAR>rand		{ SYSTEM_VERILOG_KEYWORD(TOK_RAND); }
<GRAMMAR>randc		{ SYSTEM_VERILOG_KEYWORD(TOK_RANDC); }
<GRAMMAR>randcase	{ SYSTEM_VERILOG_KEYWORD(TOK_RANDCASE); }
<GRAMMAR>randsequence	{ SYSTEM_VERILOG_KEYWORD(TOK_RANDSEQUENCE); }
<GRAMMAR>ref		{ SYSTEM_VERILOG_KEYWORD(TOK_REF); }
<GRAMMAR>return		{ SYSTEM_VERILOG_KEYWORD(TOK_RETURN); }
<GRAMMAR>s_always       { SYSTEM_VERILOG_KEYWORD(TOK_S_ALWAYS); }
<GRAMMAR>s_eventually   { SYSTEM_VERILOG_KEYWORD(TOK_S_EVENTUALLY); }
<GRAMMAR>s_nexttime     { SYSTEM_VERILOG_KEYWORD(TOK_S_NEXTTIME); }
<GRAMMAR>s_until        { SYSTEM_VERILOG_KEYWORD(TOK_S_UNTIL); }
<GRAMMAR>s_until_with   { SYSTEM_VERILOG_KEYWORD(TOK_S_UNTIL_WITH); }
<GRAMMAR>sequence	{ SYSTEM_VERILOG_KEYWORD(TOK_SEQUENCE); }
<GRAMMAR>shortint	{ SYSTEM_VERILOG_KEYWORD(TOK_SHORTINT); }
<GRAMMAR>shortreal	{ SYSTEM_VERILOG_KEYWORD(TOK_SHORTREAL); }
<GRAMMAR>solve		{ SYSTEM_VERILOG_KEYWORD(TOK_SOLVE); }
<GRAMMAR>static		{ SYSTEM_VERILOG_KEYWORD(TOK_STATIC); }
<GRAMMAR>string		{ SYSTEM_VERILOG_KEYWORD(TOK_STRING); }
<GRAMMAR>struct		{ SYSTEM_VERILOG_KEYWORD(TOK_STRUCT); }
<GRAMMAR>super		{ SYSTEM_VERILOG_KEYWORD(TOK_SUPER); }
<GRAMMAR>tagged		{ SYSTEM_VERILOG_KEYWORD(TOK_TAGGED); }
<GRAMMAR>this		{ SYSTEM_VERILOG_KEYWORD(TOK_THIS); }
<GRAMMAR>throughout	{ SYSTEM_VERILOG_KEYWORD(TOK_THROUGHOUT); }
<GRAMMAR>timeprecision	{ SYSTEM_VERILOG_KEYWORD(TOK_TIMEPRECISION); }
<GRAMMAR>timeunit	{ SYSTEM_VERILOG_KEYWORD(TOK_TIMEUNIT); }
<GRAMMAR>type		{ SYSTEM_VERILOG_KEYWORD(TOK_TYPE); }
<GRAMMAR>typedef	{ VIS_VERILOG_KEYWORD(TOK_TYPEDEF); }
<GRAMMAR>union		{ SYSTEM_VERILOG_KEYWORD(TOK_UNION); }
<GRAMMAR>unique		{ SYSTEM_VERILOG_KEYWORD(TOK_UNIQUE); }
<GRAMMAR>until          { SYSTEM_VERILOG_KEYWORD(TOK_UNTIL); }
<GRAMMAR>until_with     { SYSTEM_VERILOG_KEYWORD(TOK_UNTIL_WITH); }
<GRAMMAR>var		{ SYSTEM_VERILOG_KEYWORD(TOK_VAR); }
<GRAMMAR>virtual	{ SYSTEM_VERILOG_KEYWORD(TOK_VIRTUAL); }
<GRAMMAR>void		{ SYSTEM_VERILOG_KEYWORD(TOK_VOID); }
<GRAMMAR>wait_order	{ SYSTEM_VERILOG_KEYWORD(TOK_WAIT_ORDER); }
<GRAMMAR>wildcard	{ SYSTEM_VERILOG_KEYWORD(TOK_WILDCARD); }
<GRAMMAR>with		{ SYSTEM_VERILOG_KEYWORD(TOK_WITH); }
<GRAMMAR>within		{ SYSTEM_VERILOG_KEYWORD(TOK_WITHIN); }

	/*
	 * Others.
	 */

<GRAMMAR>\'line		{ /* get_line_number(); */ continue; }
<GRAMMAR>\'file		{ /* get_file_name(); */ continue; }
<GRAMMAR>\`line{WS}[^\n]*{NL} { line_directive(); continue; }
<GRAMMAR>\`{Word}	{ preprocessor(); continue; }
<GRAMMAR>\f		{ /* ignore */ }

<GRAMMAR>\${Word}	{ newstack(yyveriloglval); stack(yyveriloglval).id(yytext); return TOK_SYSIDENT; }
<GRAMMAR>{Binary}	{ newstack(yyveriloglval); stack(yyveriloglval).id(yytext); return TOK_NUMBER; }
<GRAMMAR>{Octal}	{ newstack(yyveriloglval); stack(yyveriloglval).id(yytext); return TOK_NUMBER; }
<GRAMMAR>{Decimal}	{ newstack(yyveriloglval); stack(yyveriloglval).id(yytext); return TOK_NUMBER; }
<GRAMMAR>{Hexdecimal}	{ newstack(yyveriloglval); stack(yyveriloglval).id(yytext); return TOK_NUMBER; }
<GRAMMAR>{Number}	{ newstack(yyveriloglval); stack(yyveriloglval).id(yytext); return TOK_NUMBER; }
<GRAMMAR>{Real}		{ newstack(yyveriloglval); stack(yyveriloglval).id(yytext); return TOK_NUMBER; }
<GRAMMAR>{RealExp}	{ newstack(yyveriloglval); stack(yyveriloglval).id(yytext); return TOK_NUMBER; }
<GRAMMAR>{Word}		{ IDENTIFIER; }
<GRAMMAR>{EscapedWord}	{ newstack(yyveriloglval); stack(yyveriloglval).id(yytext+1); return TOK_CHARSTR; }
<GRAMMAR>.		{ return yytext[0]; }

%%

int yywrap() { return 1; }
