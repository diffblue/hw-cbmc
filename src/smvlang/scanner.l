%option nounput

%{
#include <util/pragma_wdeprecated_register.def>
#include <util/pragma_wsign_compare.def>
#include <util/pragma_wnull_conversion.def>

#ifdef _WIN32
#define YY_NO_UNISTD_H
static int isatty(int) { return 0; }
#endif

#include <cstdio>
#include <cstring>

#include <util/expr.h>

#define PARSER (*smv_parser_ptr)
#define YYSTYPE unsigned

#include "smv_parser.h"
#include "smv_y.tab.h"

int yysmverror(const std::string &error);

void newlocation(YYSTYPE &x)
{
  newstack(x);
  PARSER.set_source_location(stack_expr(x));
}

%}

%pointer

%%

"/*"		{
		  int c;

		  for(;;)
		    {
		      while((c = yyinput()) != '*' && c != EOF)
			;

		      if(c == '*')
                        {
			  while((c = yyinput()) == '*')
                            ;

			  if( c == '/' ) break;
                        }

		      if (c == EOF)
                        {
			  yysmverror("EOF in comment");
			  break;
                        }
                    }
                }

"//".*          ;
"--".*          ;
"#".*		{ /* preprocessor */ }

[ \t\n]+	;

"INIT"		{ newlocation(yysmvlval); return INIT_Token; }
"TRANS"		{ newlocation(yysmvlval); return TRANS_Token; }
"SPEC"		{ newlocation(yysmvlval); return SPEC_Token; }
"LTLSPEC"	{ newlocation(yysmvlval); return LTLSPEC_Token; }
"INVAR"		{ newlocation(yysmvlval); return INVAR_Token; }
"VAR"		{ newlocation(yysmvlval); return VAR_Token; }
"ASSIGN"	{ newlocation(yysmvlval); return ASSIGN_Token; }
"DEFINE"	{ newlocation(yysmvlval); return DEFINE_Token; }
"FAIRNESS"	{ newlocation(yysmvlval); return FAIRNESS_Token; }
"MODULE"	{ newlocation(yysmvlval); return MODULE_Token; }
"EXTERN"	{ newlocation(yysmvlval); return EXTERN_Token; }

"FALSE"		{ newlocation(yysmvlval); return FALSE_Token; }
"TRUE"		{ newlocation(yysmvlval); return TRUE_Token; }

"AG"		return AG_Token;
"AF"		return AF_Token;
"AX"		return AX_Token;
"EG"		return EG_Token;
"EF"		return EF_Token;
"EX"		return EX_Token;
"E"		return E_Token;
"A"		return A_Token;
"F"		return F_Token;
"X"		return X_Token;
"G"		return G_Token;
"U"		return U_Token;
"R"		return R_Token;
"next"		return NEXT_Token;
"init"		return init_Token;
"case"		return CASE_Token;
"esac"		return ESAC_Token;
"switch"	return SWITCH_Token;
"array"		return ARRAY_Token;
"of"		return OF_Token;
"in"		return IN_Token;
"notin"		return NOTIN_Token;
"boolean"	return BOOLEAN_Token;
"mod"           return MOD_Token;
"union"		return UNION_Token;
".."		return DOTDOT_Token;
"XOR"		return XOR_Token;

[\$A-Za-z_][A-Za-z0-9_\$#-]*	{
                  newstack(yysmvlval);
                  stack_expr(yysmvlval).id(yytext);
		  return STRING_Token;
		}
\\[A-Za-z0-9_\$#-]*	{
                  newstack(yysmvlval);
                  stack_expr(yysmvlval).id(yytext);
		  return QSTRING_Token;
		}
[0-9][0-9]*	{
                  newstack(yysmvlval);
                  stack_expr(yysmvlval).id(yytext);
		  return NUMBER_Token;
		}
\"[^\"]*\"      {
                  newstack(yysmvlval);
                  std::string tmp(yytext);
                  stack_expr(yysmvlval).id(std::string(tmp, 1, tmp.size()-2));
                  return QUOTE_Token;
                }

"?"		return IF_Token;
"~"		return NOT_Token;
"!"		return NOT_Token;
"+"		return PLUS_Token;
"-"		return MINUS_Token;
"|"		return OR_Token;
"&"		return AND_Token;
"->"		return IMPLIES_Token;
"<->"		return EQUIV_Token;
"="		return EQUAL_Token;
"<="		return LE_Token;
">="		return GE_Token;
"<"		return LT_Token;
">"		return GT_Token;
"!="		return NOTEQUAL_Token;
":="		return BECOMES_Token;
"."		return DOT_Token;

.		return yytext[0];

%%

int yywrap() { return 1; }
