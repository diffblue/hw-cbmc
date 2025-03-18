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

#define token(t) { \
  newstack(yysmvlval); \
  PARSER.set_source_location(stack_expr(yysmvlval)); \
  return t; \
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

 /* Keywords from page 7 */
 /* https://nusmv.fbk.eu/userman/v27/nusmv.pdf */
"MODULE"	token(MODULE_Token);
"DEFINE"	token(DEFINE_Token);
"MDEFINE"	token(MDEFINE_Token);
"CONSTANTS"	token(CONSTANTS_Token);
"VAR"		token(VAR_Token);
"IVAR"		token(IVAR_Token);
"FROZENVAR"	token(FROZENVAR_Token);
"INIT"		token(INIT_Token);
"TRANS"		token(TRANS_Token);
"INVAR"		token(INVAR_Token);
"SPEC"		token(SPEC_Token);
"CTLSPEC"	token(CTLSPEC_Token);
"LTLSPEC"	token(LTLSPEC_Token);
"PSLSPEC"	token(PSLSPEC_Token);
"COMPUTE"	token(COMPUTE_Token);
"NAME"		token(NAME_Token);
"INVARSPEC"	token(INVARSPEC_Token);
"FAIRNESS"	token(FAIRNESS_Token);
"JUSTICE"	token(JUSTICE_Token);
"COMPASSION"	token(COMPASSION_Token);
"ISA"		token(ISA_Token);
"ASSIGN"	token(ASSIGN_Token);
"CONSTRAINT"	token(CONSTRAINT_Token);
"SIMPWFF"	token(SIMPWFF_Token);
"CTLWFF"	token(CTLWFF_Token);
"LTLWFF"	token(LTLWFF_Token);
"PSLWFF"	token(PSLWFF_Token);
"COMPWFF"	token(COMPWFF_Token);
"IN"		token(IN_Token);
"MIN"		token(MIN_Token);
"MAX"		token(MAX_Token);
"MIRROR"	token(MIRROR_Token);
"PRED"		token(PRED_Token);
"PREDICATES"	token(PREDICATES_Token);

"process"	token(process_Token);
"array"		token(array_Token);
"of"		token(of_Token);
"boolean"	token(boolean_Token);
"integer"	token(integer_Token);
"real"		token(real_Token);
"word"		token(word_Token);
"word1"		token(word1_Token);
"bool"		token(bool_Token);
"signed"	token(signed_Token);
"unsigned"	token(unsigned_Token);
"extend"	token(extend_Token);
"resize"	token(resize_Token);
"sizeof"	token(sizeof_Token);
"uwconst"	token(uwconst_Token);
"swconst"	token(swconst_Token);

"EX"		token(EX_Token);
"AX"		token(AX_Token);
"EF"		token(EF_Token);
"AF"		token(AF_Token);
"EG"		token(EG_Token);
"AG"		token(AG_Token);
"E"		token(E_Token);
"F"		token(F_Token);
"O"		token(O_Token);
"G"		token(G_Token);
"H"		token(H_Token);
"X"		token(X_Token);
"Y"		token(Y_Token);
"Z"		token(Z_Token);
"A"		token(A_Token);
"U"		token(U_Token);
"S"		token(S_Token);
"V"		token(V_Token);
"T"		token(T_Token);
"BU"		token(BU_Token);
"EBF"		token(EBF_Token);
"ABF"		token(ABF_Token);
"EBG"		token(EBG_Token);
"ABG"		token(ABG_Token);

"case"		token(case_Token);
"esac"		token(esac_Token);
"mod"           token(mod_Token);
"next"		token(next_Token);
"init"		token(init_Token);
"union"		token(union_Token);
"in"		token(in_Token);
"xor"		token(xor_Token);
"xnor"		token(xnor_Token);
"self"		token(self_Token);
"TRUE"		token(TRUE_Token);
"FALSE"		token(FALSE_Token);
"count"		token(count_Token);
"abs"		token(abs_Token);
"max"		token(max_Token);
"min"		token(min_Token);

 /* Not in the NuSMV manual */
"EXTERN"	token(EXTERN_Token);
"switch"	token(switch_Token);
"notin"		token(notin_Token);
"R"		token(R_Token);

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
"*"		return TIMES_Token;
"/"		return DIVIDE_Token;
"|"		return OR_Token;
"&"		return AND_Token;
"->"		return IMPLIES_Token;
">>"		return GTGT_Token;
"<<"		return LTLT_Token;
"<->"		return EQUIV_Token;
"="		return EQUAL_Token;
"<="		return LE_Token;
">="		return GE_Token;
"<"		return LT_Token;
">"		return GT_Token;
"!="		return NOTEQUAL_Token;
":="		return BECOMES_Token;
"."		return DOT_Token;
".."		return DOTDOT_Token;
"::"		return COLONCOLON_Token;

.		return yytext[0];

%%

int yywrap() { return 1; }
