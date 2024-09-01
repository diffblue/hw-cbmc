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

#define PARSER (*verilog_parser_ptr)
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

#define IDENTIFIER(text) \
  { newstack(yyveriloglval); \
    irep_idt irep_id = text; \
    stack_expr(yyveriloglval).id(irep_id); \
    auto name = PARSER.lookup(irep_id); \
    return name == nullptr ? TOK_NON_TYPE_IDENTIFIER : \
           name->is_type ?   TOK_TYPE_IDENTIFIER : \
                             TOK_NON_TYPE_IDENTIFIER; \
  }
#define KEYWORD(s, x) \
  { if(PARSER.parse_tree.standard >= verilog_standardt::s) \
      return x; \
    else \
      IDENTIFIER(yytext); \
  }
#define SYSTEM_VERILOG_OPERATOR(token, text) \
  { if(PARSER.parse_tree.standard >= verilog_standardt::SV2005) \
      return token; \
    else \
      yyverilogerror(text " is a System Verilog operator"); \
  }
#define VL2SMV_OR_SYSTEM_VERILOG_KEYWORD(x) \
  { if(PARSER.parse_tree.standard >= verilog_standardt::SV2005 || \
       PARSER.parse_tree.standard == verilog_standardt::V2005_SMV) \
      return x; \
    else \
      IDENTIFIER(yytext); \
  }
#define VL2SMV_VERILOG_KEYWORD(x) \
  { if(PARSER.parse_tree.standard == verilog_standardt::V2005_SMV) \
      return x; \
    else \
      IDENTIFIER(yytext); \
  }
#define VIS_OR_VL2SMV_OR_SYSTEM_VERILOG_KEYWORD(x) \
  { if(PARSER.parse_tree.standard >= verilog_standardt::SV2005 || \
       PARSER.parse_tree.standard == verilog_standardt::V2005_SMV || \
       PARSER.parse_tree.standard == verilog_standardt::V2005_VIS) \
      return x; \
    else \
      IDENTIFIER(yytext); \
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
                  stack_expr(yyveriloglval).id(PARSER.string_literal);
                  return TOK_QSTRING;
                }

   <<EOF>>      { yyverilogerror("Unterminated string constant");
                  return TOK_SCANNER_ERROR;
                }

   "\\n"        { PARSER.string_literal += '\n'; }       // NL (0x0a) */
   "\\t"        { PARSER.string_literal += '\t'; }       // HT (0x09) */
   "\\".        { PARSER.string_literal += yytext[1]; }  // ignore the backslash
   [^\\\"\n]*   { PARSER.string_literal += &yytext[0]; } // everything else

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
                  PARSER.string_literal.clear();
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
"#-#"           { SYSTEM_VERILOG_OPERATOR(TOK_HASHMINUSHASH, "#-#"); }
"#=#"           { SYSTEM_VERILOG_OPERATOR(TOK_HASHEQUALHASH, "#=#"); }
"<->"           { SYSTEM_VERILOG_OPERATOR(TOK_LESSMINUSGREATER, "<->"); }
"->"            { SYSTEM_VERILOG_OPERATOR(TOK_MINUSGREATER, "->"); }
"'"             { SYSTEM_VERILOG_OPERATOR('\'', "'"); }
"::"            { SYSTEM_VERILOG_OPERATOR(TOK_COLONCOLON, "::"); }
"==?"           { SYSTEM_VERILOG_OPERATOR(TOK_EQUALEQUALQUESTION, "==?"); }
"!=?"           { SYSTEM_VERILOG_OPERATOR(TOK_EXCLAMEQUALQUESTION, "!=?"); }
                /* Table 16-1 in 1800-2017 suggests the following tokens for sequence operators */
"[*"            { SYSTEM_VERILOG_OPERATOR(TOK_LSQASTERIC, "[*"); }
"[+"            { SYSTEM_VERILOG_OPERATOR(TOK_LSQPLUS, "[+"); }
"[="            { SYSTEM_VERILOG_OPERATOR(TOK_LSQEQUAL, "[="); }
"[->"           { SYSTEM_VERILOG_OPERATOR(TOK_LSQMINUSGREATER, "[->"); }

                /* Verilog 1364-1995 keywords */

always          { return TOK_ALWAYS; }
and             { return TOK_AND; }
assign          { return TOK_ASSIGN; }
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
vectored        { return TOK_VECTORED; }
wait            { return TOK_WAIT; }
wand            { return TOK_WAND; }
weak0           { return TOK_WEAK0; }
weak1           { return TOK_WEAK1; }
while           { return TOK_WHILE; }
wire            { return TOK_WIRE; }
wor             { return TOK_WOR; }
xnor            { return TOK_XNOR; }
xor             { return TOK_XOR; }

$setup          { return TOK_SETUP; }
$hold           { return TOK_HOLD; }
$recovery       { return TOK_RECOVERY; }
$removal        { return TOK_REMOVAL; }
$width          { return TOK_WIDTH; }
$skew           { return TOK_SKEW; }

                /* Verilog 1364-2001-noconfig keywords */

automatic       { KEYWORD(V2001_NOCONFIG, TOK_AUTOMATIC); }
endgenerate     { KEYWORD(V2001_NOCONFIG, TOK_ENDGENERATE); }
generate        { KEYWORD(V2001_NOCONFIG, TOK_GENERATE); }
genvar          { KEYWORD(V2001_NOCONFIG, TOK_GENVAR); }
localparam      { KEYWORD(V2001_NOCONFIG, TOK_LOCALPARAM); }
noshowcancelled { KEYWORD(V2001_NOCONFIG, TOK_NOSHOWCANCELLED); }
pulsestyle_ondetect { KEYWORD(V2001_NOCONFIG, TOK_PULSESTYLE_ONDETECT); }
pulsestyle_onevent { KEYWORD(V2001_NOCONFIG, TOK_PULSESTYLE_ONEVENT); }
showcancelled   { KEYWORD(V2001_NOCONFIG, TOK_SHOWCANCELLED); }
signed          { KEYWORD(V2001_NOCONFIG, TOK_SIGNED); }
unsigned        { KEYWORD(V2001_NOCONFIG, TOK_UNSIGNED); }

                /* Verilog 1364-2001-config keywords */

cell            { KEYWORD(V2001, TOK_CELL); }
config          { KEYWORD(V2001, TOK_CONFIG); }
design          { KEYWORD(V2001, TOK_DESIGN); }
endconfig       { KEYWORD(V2001, TOK_ENDCONFIG); }
incdir          { KEYWORD(V2001, TOK_INCDIR); }
include         { KEYWORD(V2001, TOK_INCLUDE); }
instance        { KEYWORD(V2001, TOK_INSTANCE); }
liblist         { KEYWORD(V2001, TOK_LIBLIST); }
library         { KEYWORD(V2001, TOK_LIBRARY); }
use             { KEYWORD(V2001, TOK_USE); }

                /* Verilog 1364-2005 keywords */

uwire           { KEYWORD(V2005, TOK_UWIRE); }

                /* System Verilog 1800-2005 Keywords */

alias           { KEYWORD(SV2005, TOK_ALIAS); }
always_comb     { KEYWORD(SV2005, TOK_ALWAYS_COMB); }
always_ff       { KEYWORD(SV2005, TOK_ALWAYS_FF); }
always_latch    { KEYWORD(SV2005, TOK_ALWAYS_LATCH); }
assert          { VIS_OR_VL2SMV_OR_SYSTEM_VERILOG_KEYWORD(TOK_ASSERT); }
assume          { VL2SMV_OR_SYSTEM_VERILOG_KEYWORD(TOK_ASSUME); }
before          { KEYWORD(SV2005, TOK_BEFORE); }
bind            { KEYWORD(SV2005, TOK_BIND); }
bins            { KEYWORD(SV2005, TOK_BINS); }
binsof          { KEYWORD(SV2005, TOK_BINSOF); }
bit             { KEYWORD(SV2005, TOK_BIT); }
break           { KEYWORD(SV2005, TOK_BREAK); }
byte            { KEYWORD(SV2005, TOK_BYTE); }
chandle         { KEYWORD(SV2005, TOK_CHANDLE); }
class           { KEYWORD(SV2005, TOK_CLASS); }
clocking        { KEYWORD(SV2005, TOK_CLOCKING); }
const           { KEYWORD(SV2005, TOK_CONST); }
constraint      { KEYWORD(SV2005, TOK_CONSTRAINT); }
context         { KEYWORD(SV2005, TOK_CONTEXT); }
continue        { KEYWORD(SV2005, TOK_CONTINUE); }
cover           { KEYWORD(SV2005, TOK_COVER); }
covergroup      { KEYWORD(SV2005, TOK_COVERGROUP); }
coverpoint      { KEYWORD(SV2005, TOK_COVERPOINT); }
cross           { KEYWORD(SV2005, TOK_CROSS); }
dist            { KEYWORD(SV2005, TOK_DIST); }
do              { KEYWORD(SV2005, TOK_DO); }
endclass        { KEYWORD(SV2005, TOK_ENDCLASS); }
endclocking     { KEYWORD(SV2005, TOK_ENDCLOCKING); }
endgroup        { KEYWORD(SV2005, TOK_ENDGROUP); }
endinterface    { KEYWORD(SV2005, TOK_ENDINTERFACE); }
endpackage      { KEYWORD(SV2005, TOK_ENDPACKAGE); }
endprogram      { KEYWORD(SV2005, TOK_ENDPROGRAM); }
endproperty     { KEYWORD(SV2005, TOK_ENDPROPERTY); }
endsequence     { KEYWORD(SV2005, TOK_ENDSEQUENCE); }
enum            { VIS_OR_VL2SMV_OR_SYSTEM_VERILOG_KEYWORD(TOK_ENUM); }
expect          { KEYWORD(SV2005, TOK_EXPECT); }
export          { KEYWORD(SV2005, TOK_EXPORT); }
extends         { KEYWORD(SV2005, TOK_EXTENDS); }
extern          { KEYWORD(SV2005, TOK_EXTERN); }
final           { KEYWORD(SV2005, TOK_FINAL); }
first_match     { KEYWORD(SV2005, TOK_FIRST_MATCH); }
foreach         { KEYWORD(SV2005, TOK_FOREACH); }
forkjoin        { KEYWORD(SV2005, TOK_FORKJOIN); }
iff             { KEYWORD(SV2005, TOK_IFF); }
ignore_bins     { KEYWORD(SV2005, TOK_IGNORE_BINS); }
illegal_bins    { KEYWORD(SV2005, TOK_ILLEGAL_BINS); }
import          { KEYWORD(SV2005, TOK_IMPORT); }
inside          { KEYWORD(SV2005, TOK_INSIDE); }
int             { KEYWORD(SV2005, TOK_INT); }
interface       { KEYWORD(SV2005, TOK_INTERFACE); }
intersect       { KEYWORD(SV2005, TOK_INTERSECT); }
join_any        { KEYWORD(SV2005, TOK_JOIN_ANY); }
join_none       { KEYWORD(SV2005, TOK_JOIN_NONE); }
local           { KEYWORD(SV2005, TOK_LOCAL); }
logic           { KEYWORD(SV2005, TOK_LOGIC); }
longint         { KEYWORD(SV2005, TOK_LONGINT); }
matches         { KEYWORD(SV2005, TOK_MATCHES); }
modport         { KEYWORD(SV2005, TOK_MODPORT); }
new             { KEYWORD(SV2005, TOK_NEW); }
null            { KEYWORD(SV2005, TOK_NULL); }
package         { KEYWORD(SV2005, TOK_PACKAGE); }
packed          { KEYWORD(SV2005, TOK_PACKED); }
priority        { KEYWORD(SV2005, TOK_PRIORITY); }
program         { KEYWORD(SV2005, TOK_PROGRAM); }
property        { KEYWORD(SV2005, TOK_PROPERTY); }
protected       { KEYWORD(SV2005, TOK_PROTECTED); }
pure            { KEYWORD(SV2005, TOK_PURE); }
rand            { KEYWORD(SV2005, TOK_RAND); }
randc           { KEYWORD(SV2005, TOK_RANDC); }
randcase        { KEYWORD(SV2005, TOK_RANDCASE); }
randsequence    { KEYWORD(SV2005, TOK_RANDSEQUENCE); }
ref             { KEYWORD(SV2005, TOK_REF); }
return          { KEYWORD(SV2005, TOK_RETURN); }
sequence        { KEYWORD(SV2005, TOK_SEQUENCE); }
shortint        { KEYWORD(SV2005, TOK_SHORTINT); }
shortreal       { KEYWORD(SV2005, TOK_SHORTREAL); }
solve           { KEYWORD(SV2005, TOK_SOLVE); }
static          { KEYWORD(SV2005, TOK_STATIC); }
string          { KEYWORD(SV2005, TOK_STRING); }
struct          { KEYWORD(SV2005, TOK_STRUCT); }
super           { KEYWORD(SV2005, TOK_SUPER); }
tagged          { KEYWORD(SV2005, TOK_TAGGED); }
this            { KEYWORD(SV2005, TOK_THIS); }
throughout      { KEYWORD(SV2005, TOK_THROUGHOUT); }
timeprecision   { KEYWORD(SV2005, TOK_TIMEPRECISION); }
timeunit        { KEYWORD(SV2005, TOK_TIMEUNIT); }
type            { KEYWORD(SV2005, TOK_TYPE); }
typedef         { VIS_OR_VL2SMV_OR_SYSTEM_VERILOG_KEYWORD(TOK_TYPEDEF); }
union           { KEYWORD(SV2005, TOK_UNION); }
unique          { KEYWORD(SV2005, TOK_UNIQUE); }
var             { KEYWORD(SV2005, TOK_VAR); }
virtual         { KEYWORD(SV2005, TOK_VIRTUAL); }
void            { KEYWORD(SV2005, TOK_VOID); }
wait_order      { KEYWORD(SV2005, TOK_WAIT_ORDER); }
wildcard        { KEYWORD(SV2005, TOK_WILDCARD); }
with            { KEYWORD(SV2005, TOK_WITH); }
within          { KEYWORD(SV2005, TOK_WITHIN); }

                /* System Verilog 1800-2009 Keywords */

accept_on       { KEYWORD(SV2009, TOK_ACCEPT_ON); }
checker         { KEYWORD(SV2009, TOK_CHECKER); }
endchecker      { KEYWORD(SV2009, TOK_ENDCHECKER); }
eventually      { VL2SMV_OR_SYSTEM_VERILOG_KEYWORD(TOK_EVENTUALLY); }
global          { KEYWORD(SV2009, TOK_GLOBAL); }
implies         { KEYWORD(SV2009, TOK_IMPLIES); }
let             { KEYWORD(SV2009, TOK_LET); }
nexttime        { KEYWORD(SV2009, TOK_NEXTTIME); }
reject_on       { KEYWORD(SV2009, TOK_REJECT_ON); }
restrict        { KEYWORD(SV2009, TOK_RESTRICT); }
s_always        { KEYWORD(SV2009, TOK_S_ALWAYS); }
s_eventually    { KEYWORD(SV2009, TOK_S_EVENTUALLY); }
s_nexttime      { KEYWORD(SV2009, TOK_S_NEXTTIME); }
s_until         { KEYWORD(SV2009, TOK_S_UNTIL); }
s_until_with    { KEYWORD(SV2009, TOK_S_UNTIL_WITH); }
strong          { KEYWORD(SV2009, TOK_STRONG); }
sync_accept_on  { KEYWORD(SV2009, TOK_SYNC_ACCEPT_ON); }
sync_reject_on  { KEYWORD(SV2009, TOK_SYNC_REJECT_ON); }
unique0         { KEYWORD(SV2009, TOK_UNIQUE0); }
until           { KEYWORD(SV2009, TOK_UNTIL); }
until_with      { KEYWORD(SV2009, TOK_UNTIL_WITH); }
untyped         { KEYWORD(SV2009, TOK_UNTYPED); }
weak            { KEYWORD(SV2009, TOK_WEAK); }

                /* System Verilog 1800-2012 Keywords */

implements      { KEYWORD(SV2012, TOK_IMPLEMENTS); }
interconnect    { KEYWORD(SV2012, TOK_INTERCONNECT); }
nettype         { KEYWORD(SV2012, TOK_NETTYPE); }
soft            { KEYWORD(SV2012, TOK_SOFT); }

                /* VL2SMV Keywords */

using           { VL2SMV_VERILOG_KEYWORD(TOK_USING); }
prove           { VL2SMV_VERILOG_KEYWORD(TOK_PROVE); }

                /* Preprocessor outputs */

\'line          { continue; }
\'file          { continue; }
\`line{WS}[^\n]*{NL} { line_directive(); continue; }
\`default_nettype{WS}[^\n]*{NL} { /* ignore for now */ continue; }
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
{Word}          { IDENTIFIER(yytext); }
{EscapedWord}   { IDENTIFIER(yytext+1); /* The backslash is not part of the name */ }
.               { return yytext[0]; }
} // GRAMMAR

%%

int yywrap() { return 1; }
