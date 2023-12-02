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

#define IDENTIFIER { newstack(yyveriloglval); stack_expr(yyveriloglval).id(yytext); return TOK_CHARSTR; }
#define SYSTEM_VERILOG_KEYWORD(x) \
  { if(PARSER.mode==verilog_parsert::SYSTEM_VERILOG) \
      return x; \
    else \
      IDENTIFIER; \
  }
#define SYSTEM_VERILOG_OPERATOR(token, text) \
  { if(PARSER.mode==verilog_parsert::SYSTEM_VERILOG) \
      return token; \
    else \
      yyverilogerror(text " is a System Verilog operator"); \
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

NL              [\n]
WS              [ \t\r\b]
WSNL            [{WS}{NL}]
Digit           [0-9]
DigitU          [0-9_]
Letter          [a-zA-Z]
LetterU         [a-zA-Z_]
WordNum         [0-9a-zA-Z]
WordNumUD       [0-9a-zA-Z_$]
WSs             {WS}+
WSst            {WS}*
Number          {Digit}{DigitU}*
Word            {LetterU}{WordNumUD}*
EscapedWord     "\\"[^\n \t\r]+
Binary          ({Number})?{WSst}'{WSst}[sS]?[bB]{WSst}[01xXzZ?]([01xXzZ?_])*
Octal           ({Number})?{WSst}'{WSst}[sS]?[oO]{WSst}[0-7xXzZ?]([0-7xXzZ?_])*
Decimal         ({Number})?{WSst}'{WSst}[sS]?[dD]{WSst}{Number}
Hexdecimal      ({Number})?{WSst}'{WSst}[sS]?[hH]{WSst}[0-9a-fA-FxXzZ?]([0-9a-fA-FxXzZ?_])*
Time            {Number}(\.{Number})?("fs"|"ps"|"ns"|"us"|"ms"|"s")
Real            {Number}\.{Number}
RealExp         {Number}(\.{Number})?[eE][+-]?{Number}
Comment         "//"[^\n]*{NL}

%{
void verilog_scanner_init()
 {
  YY_FLUSH_BUFFER;
  BEGIN 0; // INITIAL
 }
%}

%%

<INITIAL>.|\n   { BEGIN GRAMMAR;
                  yyless(0);            /* start again with this character */
                  //yy_current_buffer->yy_at_bol = 1; /* at beginning of line */
                  switch(PARSER.grammar)
                   {
                   case verilog_parsert::EXPRESSION: return TOK_PARSE_EXPRESSION;
                   case verilog_parsert::TYPE: return TOK_PARSE_TYPE;
                   case verilog_parsert::LANGUAGE: return TOK_PARSE_LANGUAGE;
                   default: assert(0);
                   }
                }

<COMMENT>{
  {NL}          { continue; }
  .             { continue; }
  "*/"          { BEGIN GRAMMAR; continue; }
} // COMMENT

<STRING>{
   "\""         { BEGIN(GRAMMAR);
                  stack_expr(yyveriloglval).id(verilog_parser.string_literal);
                  return TOK_QSTRING;
                }

   <<EOF>>      { yyverilogerror("Unterminated string constant");
                  return TOK_SCANNER_ERROR;
                }

   "\\n"        { verilog_parser.string_literal += '\n'; }      // NL (0x0a) */
   "\\t"        { verilog_parser.string_literal += '\t'; }      // HT (0x09) */
   "\\".        { verilog_parser.string_literal += yytext[1]; } // ignore the backslash
   [^\\\"\n]*   { verilog_parser.string_literal += &yytext[0]; } // everything else

   \n           { yyverilogerror("Unterminated string constant");
                  return TOK_SCANNER_ERROR;
                }
} // STRING

<GRAMMAR>{
{NL}            { continue; }
{WSs}           { continue; }
{Comment}       { continue; }
"/*"            { BEGIN COMMENT; continue; }
"\""            { BEGIN(STRING);
                  newstack(yyveriloglval);
                  verilog_parser.string_literal.clear();
                }

                /* Attributes */

"(*"            { return TOK_PARENASTERIC; }
"*)"            { return TOK_ASTERICPAREN; }

                /* Unary operators */

"+"             { return TOK_PLUS; }
"-"             { return TOK_MINUS; }
"!"             { return TOK_EXCLAM; }
"~"             { return TOK_TILDE; }
"&"             { return TOK_AMPER; }
"~&"            { return TOK_TILDEAMPER; }
"|"             { return TOK_VERTBAR; }
"~|"            { return TOK_TILDEVERTBAR; }
"^"             { return TOK_CARET; }
"~^"            { return TOK_TILDECARET; }
"^~"            { return TOK_CARETTILDE; }

                /* Binary operators */

"*"             { return TOK_ASTERIC; }
"/"             { return TOK_SLASH; }
"%"             { return TOK_PERCENT; }
"=="            { return TOK_EQUALEQUAL; }
"!="            { return TOK_EXCLAMEQUAL; }
"==="           { return TOK_EQUALEQUALEQUAL; }
"!=="           { return TOK_EXCLAMEQUALEQUAL; }
"&&"            { return TOK_AMPERAMPER; }
"||"            { return TOK_VERTBARVERTBAR; }
"**"            { return TOK_ASTERICASTERIC; }
"<"             { return TOK_LESS; }
"<="            { return TOK_LESSEQUAL; }
">"             { return TOK_GREATER; }
">="            { return TOK_GREATEREQUAL; }
">>"            { return TOK_GREATERGREATER; }
">>>"           { return TOK_GREATERGREATERGREATER; }
"<<"            { return TOK_LESSLESS; }
"<<<"           { return TOK_LESSLESSLESS; }

                /* Trinary operators */

"?"             { return TOK_QUESTION; }
":"             { return TOK_COLON; }

                /* System Verilog operators */

"|->"           { SYSTEM_VERILOG_OPERATOR(TOK_VERTBARMINUSGREATER, "|->"); }
"|=>"           { SYSTEM_VERILOG_OPERATOR(TOK_VERTBAREQUALGREATER, "|=>"); }
"++"            { SYSTEM_VERILOG_OPERATOR(TOK_PLUSPLUS, "++"); }
"--"            { SYSTEM_VERILOG_OPERATOR(TOK_MINUSMINUS, "--"); }
"+="            { SYSTEM_VERILOG_OPERATOR(TOK_PLUSEQUAL, "+="); }
"+:"            { SYSTEM_VERILOG_OPERATOR(TOK_PLUSCOLON, "+:"); }
"-:"            { SYSTEM_VERILOG_OPERATOR(TOK_MINUSCOLON, "-:"); }
"-="            { SYSTEM_VERILOG_OPERATOR(TOK_MINUSEQUAL, "-="); }
"*="            { SYSTEM_VERILOG_OPERATOR(TOK_ASTERICEQUAL, "*="); }
"/="            { SYSTEM_VERILOG_OPERATOR(TOK_SLASHEQUAL, "+="); }
"%="            { SYSTEM_VERILOG_OPERATOR(TOK_PERCENTEQUAL, "%="); }
"&="            { SYSTEM_VERILOG_OPERATOR(TOK_AMPEREQUAL, "&="); }
"^="            { SYSTEM_VERILOG_OPERATOR(TOK_CARETEQUAL, "^="); }
"|="            { SYSTEM_VERILOG_OPERATOR(TOK_VERTBAREQUAL, "|="); }
"<<="           { SYSTEM_VERILOG_OPERATOR(TOK_LESSLESSEQUAL, "<<="); }
">>="           { SYSTEM_VERILOG_OPERATOR(TOK_GREATERGREATEREQUAL, ">>="); }
"<<<="          { SYSTEM_VERILOG_OPERATOR(TOK_LESSLESSLESSEQUAL, "<<<="); }
">>>="          { SYSTEM_VERILOG_OPERATOR(TOK_GREATERGREATERGREATEREQUAL, ">>>="); }
"##"            { SYSTEM_VERILOG_OPERATOR(TOK_HASHHASH, "##"); }
"<->"           { SYSTEM_VERILOG_OPERATOR(TOK_LESSMINUSGREATER, "<->"); }
"->"            { SYSTEM_VERILOG_OPERATOR(TOK_MINUSGREATER, "->"); }

                /* Verilog keywords */

always          { return TOK_ALWAYS; }
and             { return TOK_AND; }
assign          { return TOK_ASSIGN; }
automatic       { return TOK_AUTOMATIC; }
begin           { return TOK_BEGIN; }
buf             { return TOK_BUF; }
bufif0          { return TOK_BUFIF0; }
bufif1          { return TOK_BUFIF1; }
case            { return TOK_CASE; }
casex           { return TOK_CASEX; }
casez           { return TOK_CASEZ; }
cmos            { return TOK_CMOS; }
deassign        { return TOK_DEASSIGN; }
default         { return TOK_DEFAULT; }
defparam        { return TOK_DEFPARAM; }
disable         { return TOK_DISABLE; }
edge            { return TOK_EDGE; }
else            { return TOK_ELSE; }
end             { return TOK_END; }
endcase         { return TOK_ENDCASE; }
endfunction     { return TOK_ENDFUNCTION; }
endgenerate     { return TOK_ENDGENERATE; }
endmodule       { return TOK_ENDMODULE; }
endprimitive    { return TOK_ENDPRIMITIVE; }
endspecify      { return TOK_ENDSPECIFY; }
endtable        { return TOK_ENDTABLE; }
endtask         { return TOK_ENDTASK; }
event           { return TOK_EVENT; }
for             { return TOK_FOR; }
force           { return TOK_FORCE; }
forever         { return TOK_FOREVER; }
fork            { return TOK_FORK; }
function        { return TOK_FUNCTION; }
generate        { return TOK_GENERATE; }
genvar          { return TOK_GENVAR; }
highz0          { return TOK_HIGHZ0; }
highz1          { return TOK_HIGHZ1; }
if              { return TOK_IF; }
ifnone          { return TOK_IFNONE; }
initial         { return TOK_INITIAL; }
inout           { return TOK_INOUT; }
input           { return TOK_INPUT; }
integer         { return TOK_INTEGER; }
join            { return TOK_JOIN; }
large           { return TOK_LARGE; }
localparam      { return TOK_LOCALPARAM; }
macromodule     { return TOK_MACROMODULE; }
medium          { return TOK_MEDIUM; }
module          { return TOK_MODULE; }
nand            { return TOK_NAND; }
negedge         { return TOK_NEGEDGE; }
nmos            { return TOK_NMOS; }
nor             { return TOK_NOR; }
not             { return TOK_NOT; }
notif0          { return TOK_NOTIF0; }
notif1          { return TOK_NOTIF1; }
or              { return TOK_OR; }
output          { return TOK_OUTPUT; }
parameter       { return TOK_PARAMETER; }
pmos            { return TOK_PMOS; }
posedge         { return TOK_POSEDGE; }
primitive       { return TOK_PRIMITIVE; }
pull0           { return TOK_PULL0; }
pull1           { return TOK_PULL1; }
pulldown        { return TOK_PULLDOWN; }
pullup          { return TOK_PULLUP; }
rcmos           { return TOK_RCMOS; }
real            { return TOK_REAL; }
realtime        { return TOK_REALTIME; }
reg             { return TOK_REG; }
release         { return TOK_RELEASE; }
repeat          { return TOK_REPEAT; }
rnmos           { return TOK_RNMOS; }
rpmos           { return TOK_RPMOS; }
rtran           { return TOK_RTRAN; }
rtranif0        { return TOK_RTRANIF0; }
rtranif1        { return TOK_RTRANIF1; }
scalared        { return TOK_SCALARED; }
signed          { return TOK_SIGNED; }
small           { return TOK_SMALL; }
specify         { return TOK_SPECIFY; }
specparam       { return TOK_SPECPARAM; }
strong0         { return TOK_STRONG0; }
strong1         { return TOK_STRONG1; }
supply0         { return TOK_SUPPLY0; }
supply1         { return TOK_SUPPLY1; }
table           { return TOK_TABLE; }
task            { return TOK_TASK; }
time            { return TOK_TIME; }
tran            { return TOK_TRAN; }
tranif0         { return TOK_TRANIF0; }
tranif1         { return TOK_TRANIF1; }
tri             { return TOK_TRI; }
tri0            { return TOK_TRI0; }
tri1            { return TOK_TRI1; }
triand          { return TOK_TRIAND; }
trior           { return TOK_TRIOR; }
trireg          { return TOK_TRIREG; }
uwire           { return TOK_UWIRE; } // Verilog 2005
vectored        { return TOK_VECTORED; }
wait            { return TOK_WAIT; }
wand            { return TOK_WAND; }
weak0           { return TOK_WEAK0; }
weak1           { return TOK_WEAK1; }
wor             { return TOK_WOR; }
while           { return TOK_WHILE; }
wire            { return TOK_WIRE; }
xnor            { return TOK_XNOR; }
xor             { return TOK_XOR; }
$setup          { return TOK_SETUP; }
$hold           { return TOK_HOLD; }
$recovery       { return TOK_RECOVERY; }
$removal        { return TOK_REMOVAL; }
$width          { return TOK_WIDTH; }
$skew           { return TOK_SKEW; }

                /* System Verilog Keywords */

accept_on       { SYSTEM_VERILOG_KEYWORD(TOK_ACCEPT_ON); }
alias           { SYSTEM_VERILOG_KEYWORD(TOK_ALIAS); }
always_comb     { SYSTEM_VERILOG_KEYWORD(TOK_ALWAYS_COMB); }
always_ff       { SYSTEM_VERILOG_KEYWORD(TOK_ALWAYS_FF); }
always_latch    { SYSTEM_VERILOG_KEYWORD(TOK_ALWAYS_LATCH); }
assert          { VIS_VERILOG_KEYWORD(TOK_ASSERT); }
assume          { VIS_VERILOG_KEYWORD(TOK_ASSUME); }
before          { SYSTEM_VERILOG_KEYWORD(TOK_BEFORE); }
bind            { SYSTEM_VERILOG_KEYWORD(TOK_BIND); }
bins            { SYSTEM_VERILOG_KEYWORD(TOK_BINS); }
binsof          { SYSTEM_VERILOG_KEYWORD(TOK_BINSOF); }
bit             { SYSTEM_VERILOG_KEYWORD(TOK_BIT); }
break           { SYSTEM_VERILOG_KEYWORD(TOK_BREAK); }
byte            { SYSTEM_VERILOG_KEYWORD(TOK_BYTE); }
cell            { SYSTEM_VERILOG_KEYWORD(TOK_CELL); }
chandle         { SYSTEM_VERILOG_KEYWORD(TOK_CHANDLE); }
checker         { SYSTEM_VERILOG_KEYWORD(TOK_CHECKER); }
class           { SYSTEM_VERILOG_KEYWORD(TOK_CLASS); }
clocking        { SYSTEM_VERILOG_KEYWORD(TOK_CLOCKING); }
config          { SYSTEM_VERILOG_KEYWORD(TOK_CONFIG); }
const           { SYSTEM_VERILOG_KEYWORD(TOK_CONST); }
constraint      { SYSTEM_VERILOG_KEYWORD(TOK_CONSTRAINT); }
context         { SYSTEM_VERILOG_KEYWORD(TOK_CONTEXT); }
continue        { SYSTEM_VERILOG_KEYWORD(TOK_CONTINUE); }
cover           { SYSTEM_VERILOG_KEYWORD(TOK_COVER); }
covergroup      { SYSTEM_VERILOG_KEYWORD(TOK_COVERGROUP); }
coverpoint      { SYSTEM_VERILOG_KEYWORD(TOK_COVERPOINT); }
cross           { SYSTEM_VERILOG_KEYWORD(TOK_CROSS); }
design          { SYSTEM_VERILOG_KEYWORD(TOK_DESIGN); }
dist            { SYSTEM_VERILOG_KEYWORD(TOK_DIST); }
do              { SYSTEM_VERILOG_KEYWORD(TOK_DO); }
endchecker      { SYSTEM_VERILOG_KEYWORD(TOK_ENDCHECKER); }
endclass        { SYSTEM_VERILOG_KEYWORD(TOK_ENDCLASS); }
endclocking     { SYSTEM_VERILOG_KEYWORD(TOK_ENDCLOCKING); }
endgroup        { SYSTEM_VERILOG_KEYWORD(TOK_ENDGROUP); }
endinterface    { SYSTEM_VERILOG_KEYWORD(TOK_ENDINTERFACE); }
endpackage      { SYSTEM_VERILOG_KEYWORD(TOK_ENDPACKAGE); }
endprogram      { SYSTEM_VERILOG_KEYWORD(TOK_ENDPROGRAM); }
endproperty     { SYSTEM_VERILOG_KEYWORD(TOK_ENDPROPERTY); }
endsequence     { SYSTEM_VERILOG_KEYWORD(TOK_ENDSEQUENCE); }
enum            { VIS_VERILOG_KEYWORD(TOK_ENUM); }
eventually      { SYSTEM_VERILOG_KEYWORD(TOK_EVENTUALLY); }
expect          { SYSTEM_VERILOG_KEYWORD(TOK_EXPECT); }
export          { SYSTEM_VERILOG_KEYWORD(TOK_EXPORT); }
extends         { SYSTEM_VERILOG_KEYWORD(TOK_EXTENDS); }
extern          { SYSTEM_VERILOG_KEYWORD(TOK_EXTERN); }
final           { SYSTEM_VERILOG_KEYWORD(TOK_FINAL); }
first_match     { SYSTEM_VERILOG_KEYWORD(TOK_FIRST_MATCH); }
foreach         { SYSTEM_VERILOG_KEYWORD(TOK_FOREACH); }
iff             { SYSTEM_VERILOG_KEYWORD(TOK_IFF); }
ignore_bins     { SYSTEM_VERILOG_KEYWORD(TOK_IGNORE_BINS); }
illegal_bins    { SYSTEM_VERILOG_KEYWORD(TOK_ILLEGAL_BINS); }
implements      { SYSTEM_VERILOG_KEYWORD(TOK_IMPLEMENTS); }
implies         { SYSTEM_VERILOG_KEYWORD(TOK_IMPLIES); }
import          { SYSTEM_VERILOG_KEYWORD(TOK_IMPORT); }
inside          { SYSTEM_VERILOG_KEYWORD(TOK_INSIDE); }
int             { SYSTEM_VERILOG_KEYWORD(TOK_INT); }
interface       { SYSTEM_VERILOG_KEYWORD(TOK_INTERFACE); }
intersect       { SYSTEM_VERILOG_KEYWORD(TOK_INTERSECT); }
join_any        { SYSTEM_VERILOG_KEYWORD(TOK_JOIN_ANY); }
join_none       { SYSTEM_VERILOG_KEYWORD(TOK_JOIN_NONE); }
local           { SYSTEM_VERILOG_KEYWORD(TOK_LOCAL); }
logic           { SYSTEM_VERILOG_KEYWORD(TOK_LOGIC); }
longint         { SYSTEM_VERILOG_KEYWORD(TOK_LONGINT); }
matches         { SYSTEM_VERILOG_KEYWORD(TOK_MATCHES); }
modport         { SYSTEM_VERILOG_KEYWORD(TOK_MODPORT); }
new             { SYSTEM_VERILOG_KEYWORD(TOK_NEW); }
nexttime        { SYSTEM_VERILOG_KEYWORD(TOK_NEXTTIME); }
null            { SYSTEM_VERILOG_KEYWORD(TOK_NULL); }
package         { SYSTEM_VERILOG_KEYWORD(TOK_PACKAGE); }
packed          { SYSTEM_VERILOG_KEYWORD(TOK_PACKED); }
priority        { SYSTEM_VERILOG_KEYWORD(TOK_PRIORITY); }
program         { SYSTEM_VERILOG_KEYWORD(TOK_PROGRAM); }
property        { SYSTEM_VERILOG_KEYWORD(TOK_PROPERTY); }
protected       { SYSTEM_VERILOG_KEYWORD(TOK_PROTECTED); }
pure            { SYSTEM_VERILOG_KEYWORD(TOK_PURE); }
rand            { SYSTEM_VERILOG_KEYWORD(TOK_RAND); }
randc           { SYSTEM_VERILOG_KEYWORD(TOK_RANDC); }
randcase        { SYSTEM_VERILOG_KEYWORD(TOK_RANDCASE); }
randsequence    { SYSTEM_VERILOG_KEYWORD(TOK_RANDSEQUENCE); }
ref             { SYSTEM_VERILOG_KEYWORD(TOK_REF); }
return          { SYSTEM_VERILOG_KEYWORD(TOK_RETURN); }
s_always        { SYSTEM_VERILOG_KEYWORD(TOK_S_ALWAYS); }
s_eventually    { SYSTEM_VERILOG_KEYWORD(TOK_S_EVENTUALLY); }
s_nexttime      { SYSTEM_VERILOG_KEYWORD(TOK_S_NEXTTIME); }
s_until         { SYSTEM_VERILOG_KEYWORD(TOK_S_UNTIL); }
s_until_with    { SYSTEM_VERILOG_KEYWORD(TOK_S_UNTIL_WITH); }
sequence        { SYSTEM_VERILOG_KEYWORD(TOK_SEQUENCE); }
shortint        { SYSTEM_VERILOG_KEYWORD(TOK_SHORTINT); }
shortreal       { SYSTEM_VERILOG_KEYWORD(TOK_SHORTREAL); }
showcancelled   { SYSTEM_VERILOG_KEYWORD(TOK_SHOWCANCELLED); }
solve           { SYSTEM_VERILOG_KEYWORD(TOK_SOLVE); }
static          { SYSTEM_VERILOG_KEYWORD(TOK_STATIC); }
string          { SYSTEM_VERILOG_KEYWORD(TOK_STRING); }
struct          { SYSTEM_VERILOG_KEYWORD(TOK_STRUCT); }
super           { SYSTEM_VERILOG_KEYWORD(TOK_SUPER); }
tagged          { SYSTEM_VERILOG_KEYWORD(TOK_TAGGED); }
this            { SYSTEM_VERILOG_KEYWORD(TOK_THIS); }
throughout      { SYSTEM_VERILOG_KEYWORD(TOK_THROUGHOUT); }
timeprecision   { SYSTEM_VERILOG_KEYWORD(TOK_TIMEPRECISION); }
timeunit        { SYSTEM_VERILOG_KEYWORD(TOK_TIMEUNIT); }
type            { SYSTEM_VERILOG_KEYWORD(TOK_TYPE); }
typedef         { VIS_VERILOG_KEYWORD(TOK_TYPEDEF); }
union           { SYSTEM_VERILOG_KEYWORD(TOK_UNION); }
unique          { SYSTEM_VERILOG_KEYWORD(TOK_UNIQUE); }
unique0         { SYSTEM_VERILOG_KEYWORD(TOK_UNIQUE0); }
until           { SYSTEM_VERILOG_KEYWORD(TOK_UNTIL); }
until_with      { SYSTEM_VERILOG_KEYWORD(TOK_UNTIL_WITH); }
untyped         { SYSTEM_VERILOG_KEYWORD(TOK_UNTYPED); }
var             { SYSTEM_VERILOG_KEYWORD(TOK_VAR); }
virtual         { SYSTEM_VERILOG_KEYWORD(TOK_VIRTUAL); }
void            { SYSTEM_VERILOG_KEYWORD(TOK_VOID); }
wait_order      { SYSTEM_VERILOG_KEYWORD(TOK_WAIT_ORDER); }
wildcard        { SYSTEM_VERILOG_KEYWORD(TOK_WILDCARD); }
with            { SYSTEM_VERILOG_KEYWORD(TOK_WITH); }
within          { SYSTEM_VERILOG_KEYWORD(TOK_WITHIN); }

                /* Preprocessor outputs */

\'line          { continue; }
\'file          { continue; }
\`line{WS}[^\n]*{NL} { line_directive(); continue; }
\`{Word}        { preprocessor(); continue; }

\f              { /* ignore */ }

                /* Identifiers and numbers */

\${Word}        { newstack(yyveriloglval); stack_expr(yyveriloglval).id(yytext); return TOK_SYSIDENT; }
{Binary}        { newstack(yyveriloglval); stack_expr(yyveriloglval).id(yytext); return TOK_NUMBER; }
{Octal}         { newstack(yyveriloglval); stack_expr(yyveriloglval).id(yytext); return TOK_NUMBER; }
{Decimal}       { newstack(yyveriloglval); stack_expr(yyveriloglval).id(yytext); return TOK_NUMBER; }
{Hexdecimal}    { newstack(yyveriloglval); stack_expr(yyveriloglval).id(yytext); return TOK_NUMBER; }
{Number}        { newstack(yyveriloglval); stack_expr(yyveriloglval).id(yytext); return TOK_NUMBER; }
{Time}		{ newstack(yyveriloglval); stack_expr(yyveriloglval).id(yytext); return TOK_TIME_LITERAL; }
{Real}          { newstack(yyveriloglval); stack_expr(yyveriloglval).id(yytext); return TOK_NUMBER; }
{RealExp}       { newstack(yyveriloglval); stack_expr(yyveriloglval).id(yytext); return TOK_NUMBER; }
{Word}          { IDENTIFIER; }
{EscapedWord}   { newstack(yyveriloglval); stack_expr(yyveriloglval).id(yytext+1); return TOK_CHARSTR; }
.               { return yytext[0]; }
} // GRAMMAR

%%

int yywrap() { return 1; }
