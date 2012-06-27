%{

#include "../util/dstring.h"

#define PARSER vhdl_parser
#define YYSTYPE unsigned

#include "vhdl_parser.h"
#include "y.tab.h"

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

[ \n\r\t] { /* eat */ }

"ABS" { return TOK_ABS; }
"ACCESS" { return TOK_ACCESS; }
"AFTER" { return TOK_AFTER; }
"ALIAS" { return TOK_ALIAS; }
"ALL" { return TOK_ALL; }
"AND" { return TOK_AND; }
"ARCHITECTURE" { return TOK_ARCHITECTURE; }
"ARRAY" { return TOK_ARRAY; }
"ASSERT" { return TOK_ASSERT; }
"ATTRIBUTE" { return TOK_ATTRIBUTE; }
"BEGIN" { return TOK_BEGIN; }
"BLOCK" { return TOK_BLOCK; }
"BODY" { return TOK_BODY; }
"BUFFER" { return TOK_BUFFER; }
"BUS" { return TOK_BUS; }
"CASE" { return TOK_CASE; }
"COMPONENT" { return TOK_COMPONENT; }
"CONFIGURATION" { return TOK_CONFIGURATION; }
"CONSTANT" { return TOK_CONSTANT; }
"DISCONNENT" { return TOK_DISCONNENT; }
"DOWNTO" { return TOK_DOWNTO; }
"ELSE" { return TOK_ELSE; }
"ELSIF" { return TOK_ELSIF; }
"END" { return TOK_END; }
"ENTITY" { return TOK_ENTITY; }
"EXIT" { return TOK_EXIT; }
"FILE" { return TOK_FILE; }
"FOR" { return TOK_FOR; }
"FUNCTION" { return TOK_FUNCTION; }
"GENERATE" { return TOK_GENERATE; }
"GENERIC" { return TOK_GENERIC; }
"GROUP" { return TOK_GROUP; }
"GUARDED" { return TOK_GUARDED; }
"IF" { return TOK_IF; }
"IMPURE" { return TOK_IMPURE; }
"IN" { return TOK_IN; }
"INERTIAL" { return TOK_INERTIAL; }
"INOUT" { return TOK_INOUT; }
"IS" { return TOK_IS; }
"LABEL" { return TOK_LABEL; }
"LIBRARY" { return TOK_LIBRARY; }
"LINKAGE" { return TOK_LINKAGE; }
"LITERAL" { return TOK_LITERAL; }
"LOOP" { return TOK_LOOP; }
"MAP" { return TOK_MAP; }
"MOD" { return TOK_MOD; }
"NAND" { return TOK_NAND; }
"NEW" { return TOK_NEW; }
"NEXT" { return TOK_NEXT; }
"NOR" { return TOK_NOR; }
"NOT" { return TOK_NOT; }
"NULL" { return TOK_NULL; }
"OF" { return TOK_OF; }
"ON" { return TOK_ON; }
"OPEN" { return TOK_OPEN; }
"OR" { return TOK_OR; }
"OTHERS" { return TOK_OTHERS; }
"OUT" { return TOK_OUT; }
"PACKAGE" { return TOK_PACKAGE; }
"PORT" { return TOK_PORT; }
"POSTPONED" { return TOK_POSTPONED; }
"PROCEDURE" { return TOK_PROCEDURE; }
"PROCESS" { return TOK_PROCESS; }
"PROTECTED" { return TOK_PROTECTED; }
"PURE" { return TOK_PURE; }
"RANGE" { return TOK_RANGE; }
"RECORD" { return TOK_RECORD; }
"REGISTER" { return TOK_REGISTER; }
"REJECT" { return TOK_REJECT; }
"REM" { return TOK_REM; }
"REPORT" { return TOK_REPORT; }
"RETURN" { return TOK_RETURN; }
"ROL" { return TOK_ROL; }
"ROR" { return TOK_ROR; }
"SELECT" { return TOK_SELECT; }
"SEVERITY" { return TOK_SEVERITY; }
"SIGNAL" { return TOK_SIGNAL; }
"SLA" { return TOK_SLA; }
"SLL" { return TOK_SLL; }
"SRA" { return TOK_SRA; }
"SRL" { return TOK_SRL; }
"SUBTYPE" { return TOK_SUBTYPE; }
"THEN" { return TOK_THEN; }
"TO" { return TOK_TO; }
"TRANSPORT" { return TOK_TRANSPORT; }
"TYPE" { return TOK_TYPE; }
"UNAFFECTED" { return TOK_UNAFFECTED; }
"UNITS" { return TOK_UNITS; }
"UNTIL" { return TOK_UNTIL; }
"USE" { return TOK_USE; }
"VARIABLE" { return TOK_VARIABLE; }
"WAIT" { return TOK_WAIT; }
"WHEN" { return TOK_WHEN; }
"WHILE" { return TOK_WHILE; }
"WITH" { return TOK_WITH; }
"XNOR" { return TOK_XNOR; }
"XOR" { return TOK_XOR; }

\"[ \!#-~]*\" {
  newstack(yyvhdllval);
  stack(yyvhdllval).id(yytext);
  return TOK_STRING;
}

[bBoOxX]\"[ \!#-~]*\" {
  newstack(yyvhdllval);
  stack(yyvhdllval).id(yytext);
  return TOK_BIT_STRING;
}

\'[0-9A-Za-z]\' { 
  newstack(yyvhdllval);
  stack(yyvhdllval).id(yytext);
  return TOK_CHAR;
}

#[0-9a-f]*# {
  newstack(yyvhdllval);
  stack(yyvhdllval).id(yytext);
  return TOK_BASED_INTEGER;
}

[a-zA-Z_$][a-zA-Z0-9_$]* {
  newstack(yyvhdllval);
  stack(yyvhdllval).id(yytext);
  return TOK_IDENTIFIER;
} 

[0-9]+ { 
  newstack(yyvhdllval);
  stack(yyvhdllval).id(yytext);
  return TOK_NATURAL;
}

. { return yytext[0]; }

%%

int yywrap() { return 1; }

