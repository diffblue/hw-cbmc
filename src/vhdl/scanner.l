%option nounput
%option noinput

%{
#ifdef _WIN32
#define YY_NO_UNISTD_H
static int isatty(int) { return 0; }
#endif

#include <util/dstring.h>

#define PARSER vhdl_parser
#define YYSTYPE vhdl_parsert::yystypet
#define set_loc() PARSER.set_location(yyvhdllval, yyleng)

#include "vhdl_parser.h"
#include "vhdl_y.tab.h"

void vhdl_scanner_init()
{
}

%}

%%

"--".*\n|"--".* {
  // we actually collect comments!

  char *tmp=yytext+2;

  while(tmp[0]==' ' || tmp[0]=='\t')
    tmp++;

  char *tmp2=tmp;
  
  while(tmp2[0]!='\n' && tmp2[0]!=0)
    tmp2++;
  
  vhdl_parser.comments.push_back(std::string(tmp, 0, tmp2-tmp));
}                                                

"=>"            { set_loc(); return TOK_ARROW; }
"**"            { set_loc(); return TOK_DOUBLE_STAR; }
":="            { set_loc(); return TOK_ASSIGN; }
"/="            { set_loc(); return TOK_NE; }
">="            { set_loc(); return TOK_GE; }
"<="            { set_loc(); return TOK_LE; }
"<<"            { set_loc(); return TOK_LEFT_LABEL_BRACKET; }
">>"            { set_loc(); return TOK_RIGHT_LABEL_BRACKET; }
"<>"            { set_loc(); return TOK_BOX; }

[ \n\r\t] { /* eat */ }

"ABS"           { set_loc(); return TOK_ABS; }
"ACCESS"        { set_loc(); return TOK_ACCESS; }
"AFTER"         { set_loc(); return TOK_AFTER; }
"ALIAS"         { set_loc(); return TOK_ALIAS; }
"ALL"           { set_loc(); return TOK_ALL; }
"AND"           { set_loc(); return TOK_AND; }
"ARCHITECTURE"  { set_loc(); return TOK_ARCHITECTURE; }
"ARRAY"         { set_loc(); return TOK_ARRAY; }
"ASSERT"        { set_loc(); return TOK_ASSERT; }
"ATTRIBUTE"     { set_loc(); return TOK_ATTRIBUTE; }
"BEGIN"         { set_loc(); return TOK_BEGIN; }
"BLOCK"         { set_loc(); return TOK_BLOCK; }
"BODY"          { set_loc(); return TOK_BODY; }
"BUFFER"        { set_loc(); return TOK_BUFFER; }
"BUS"           { set_loc(); return TOK_BUS; }
"CASE"          { set_loc(); return TOK_CASE; }
"COMPONENT"     { set_loc(); return TOK_COMPONENT; }
"CONFIGURATION" { set_loc(); return TOK_CONFIGURATION; }
"CONSTANT"      { set_loc(); return TOK_CONSTANT; }
"DISCONNENT"    { set_loc(); return TOK_DISCONNENT; }
"DOWNTO"        { set_loc(); return TOK_DOWNTO; }
"ELSE"          { set_loc(); return TOK_ELSE; }
"ELSIF"         { set_loc(); return TOK_ELSIF; }
"END"           { set_loc(); return TOK_END; }
"ENTITY"        { set_loc(); return TOK_ENTITY; }
"EXIT"          { set_loc(); return TOK_EXIT; }
"FILE"          { set_loc(); return TOK_FILE; }
"FOR"           { set_loc(); return TOK_FOR; }
"FUNCTION"      { set_loc(); return TOK_FUNCTION; }
"GENERATE"      { set_loc(); return TOK_GENERATE; }
"GENERIC"       { set_loc(); return TOK_GENERIC; }
"GROUP"         { set_loc(); return TOK_GROUP; }
"GUARDED"       { set_loc(); return TOK_GUARDED; }
"IF"            { set_loc(); return TOK_IF; }
"IMPURE"        { set_loc(); return TOK_IMPURE; }
"IN"            { set_loc(); return TOK_IN; }
"INERTIAL"      { set_loc(); return TOK_INERTIAL; }
"INOUT"         { set_loc(); return TOK_INOUT; }
"IS"            { set_loc(); return TOK_IS; }
"LABEL"         { set_loc(); return TOK_LABEL; }
"LIBRARY"       { set_loc(); return TOK_LIBRARY; }
"LINKAGE"       { set_loc(); return TOK_LINKAGE; }
"LITERAL"       { set_loc(); return TOK_LITERAL; }
"LOOP"          { set_loc(); return TOK_LOOP; }
"MAP"           { set_loc(); return TOK_MAP; }
"MOD"           { set_loc(); return TOK_MOD; }
"NAND"          { set_loc(); return TOK_NAND; }
"NEW"           { set_loc(); return TOK_NEW; }
"NEXT"          { set_loc(); return TOK_NEXT; }
"NOR"           { set_loc(); return TOK_NOR; }
"NOT"           { set_loc(); return TOK_NOT; }
"NULL"          { set_loc(); return TOK_NULL; }
"OF"            { set_loc(); return TOK_OF; }
"ON"            { set_loc(); return TOK_ON; }
"OPEN"          { set_loc(); return TOK_OPEN; }
"OR"            { set_loc(); return TOK_OR; }
"OTHERS"        { set_loc(); return TOK_OTHERS; }
"OUT"           { set_loc(); return TOK_OUT; }
"PACKAGE"       { set_loc(); return TOK_PACKAGE; }
"PORT"          { set_loc(); return TOK_PORT; }
"POSTPONED"     { set_loc(); return TOK_POSTPONED; }
"PROCEDURE"     { set_loc(); return TOK_PROCEDURE; }
"PROCESS"       { set_loc(); return TOK_PROCESS; }
"PROTECTED"     { set_loc(); return TOK_PROTECTED; }
"PURE"          { set_loc(); return TOK_PURE; }
"RANGE"         { set_loc(); return TOK_RANGE; }
"RECORD"        { set_loc(); return TOK_RECORD; }
"REGISTER"      { set_loc(); return TOK_REGISTER; }
"REJECT"        { set_loc(); return TOK_REJECT; }
"REM"           { set_loc(); return TOK_REM; }
"REPORT"        { set_loc(); return TOK_REPORT; }
"RETURN"        { set_loc(); return TOK_RETURN; }
"ROL"           { set_loc(); return TOK_ROL; }
"ROR"           { set_loc(); return TOK_ROR; }
"SELECT"        { set_loc(); return TOK_SELECT; }
"SEVERITY"      { set_loc(); return TOK_SEVERITY; }
"SIGNAL"        { set_loc(); return TOK_SIGNAL; }
"SLA"           { set_loc(); return TOK_SLA; }
"SLL"           { set_loc(); return TOK_SLL; }
"SRA"           { set_loc(); return TOK_SRA; }
"SRL"           { set_loc(); return TOK_SRL; }
"SUBTYPE"       { set_loc(); return TOK_SUBTYPE; }
"THEN"          { set_loc(); return TOK_THEN; }
"TO"            { set_loc(); return TOK_TO; }
"TRANSPORT"     { set_loc(); return TOK_TRANSPORT; }
"TYPE"          { set_loc(); return TOK_TYPE; }
"UNAFFECTED"    { set_loc(); return TOK_UNAFFECTED; }
"UNITS"         { set_loc(); return TOK_UNITS; }
"UNTIL"         { set_loc(); return TOK_UNTIL; }
"USE"           { set_loc(); return TOK_USE; }
"VARIABLE"      { set_loc(); return TOK_VARIABLE; }
"WAIT"          { set_loc(); return TOK_WAIT; }
"WHEN"          { set_loc(); return TOK_WHEN; }
"WHILE"         { set_loc(); return TOK_WHILE; }
"WITH"          { set_loc(); return TOK_WITH; }
"XNOR"          { set_loc(); return TOK_XNOR; }
"XOR"           { set_loc(); return TOK_XOR; }

\"[ \!#-~]*\" {
  set_loc();
  yyvhdllval.text=yytext;
  return TOK_STRING;
}

[bBoOxX]\"[ \!#-~]*\" {
  set_loc();
  yyvhdllval.text=yytext;
  return TOK_BIT_STRING;
}

\'[0-9A-Za-z]\' { 
  set_loc();
  yytext[2]=0;
  yyvhdllval.text=yytext+1;
  return TOK_CHAR;
}

#[0-9a-f]*# {
  set_loc();
  yyvhdllval.text=yytext;
  return TOK_BASED_INTEGER;
}

[a-zA-Z_$][a-zA-Z0-9_$]* {
  set_loc();
  yyvhdllval.text=yytext;
  return TOK_IDENTIFIER;
} 

[0-9]+ { 
  set_loc();
  yyvhdllval.text=yytext;
  return TOK_NATURAL;
}

. { set_loc(); return yytext[0]; }

%%

int yywrap() { return 1; }

