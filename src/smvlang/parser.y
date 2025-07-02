/* increase verbosity of error messages, to include expected tokens */
%define parse.error verbose

%{
#include "smv_parser.h"
#include "smv_typecheck.h"

#include <util/mathematical_types.h>
#include <util/std_expr.h>
#include <util/std_types.h>

#define YYSTYPE unsigned
#define PARSER (*smv_parser_ptr)

#include "smv_y.tab.h"

#define YYMAXDEPTH 200000
#define YYSTYPE_IS_TRIVIAL 1

/*------------------------------------------------------------------------*/

#define yylineno yysmvlineno
#define yytext yysmvtext

#define yyerror yysmverror
int yysmverror(const std::string &error);
int yylex();
extern char *yytext;

/*------------------------------------------------------------------------*/

#define mto(x, y) stack_expr(x).add_to_operands(std::move(stack_expr(y)))

  /*******************************************************************\

  Function: init

    Inputs:

   Outputs:

   Purpose:

  \*******************************************************************/

  static void init(exprt & expr) {
    expr.clear();
    PARSER.set_source_location(expr);
}

/*******************************************************************\

Function: init

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static void init(YYSTYPE &expr)
{
  newstack(expr);
  init(stack_expr(expr));
}

/*******************************************************************\

Function: init

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

 static void init(YYSTYPE &expr, const irep_idt &id)
{
  init(expr);
  stack_expr(expr).id(id);
}

 /// binary TODO[docu]
 static void binary(YYSTYPE & x_result, YYSTYPE & y_lhs, const irep_idt &id,
                    YYSTYPE &z_rhs)
 {
   init(x_result, id);
   auto &lhs = stack_expr(y_lhs);
   auto &rhs = stack_expr(z_rhs);
   stack_expr(x_result).add_to_operands(std::move(lhs), std::move(rhs));
 }

/*******************************************************************\

Function: j_binary

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static void j_binary(YYSTYPE & dest, YYSTYPE & op1, const irep_idt &id, YYSTYPE &op2)
{
  if(stack_expr(op1).id() == id)
  {
    dest = op1;
    mto(dest, op2);
  }
  else if(stack_expr(op2).id() == id)
  {
    dest = op2;
    mto(dest, op1);
  }
  else
    binary(dest, op1, id, op2);
}

/*******************************************************************\

Function: new_module

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static void new_module(YYSTYPE &module)
{
  const std::string name=smv_module_symbol(stack_expr(module).id_string());
  PARSER.module=&PARSER.parse_tree.modules[name];
  PARSER.module->name=name;
  PARSER.module->base_name=stack_expr(module).id_string();
}

/*------------------------------------------------------------------------*/

%}

/* Keywords from page 7 */
/* https://nusmv.fbk.eu/userman/v27/nusmv.pdf */
%token MODULE_Token	"MODULE"
%token DEFINE_Token	"DEFINE"
%token MDEFINE_Token	"MDEFINE"
%token CONSTANTS_Token	"CONSTANTS"
%token VAR_Token	"VAR"
%token IVAR_Token	"IVAR"
%token FROZENVAR_Token	"FROZENVAR"
%token INIT_Token	"INIT"
%token TRANS_Token	"TRANS"
%token INVAR_Token	"INVAR"
%token SPEC_Token	"SPEC"
%token CTLSPEC_Token	"CTLSPEC"
%token LTLSPEC_Token	"LTLSPEC"
%token PSLSPEC_Token	"PSLSPEC"
%token COMPUTE_Token	"COMPUTE"
%token NAME_Token	"NAME"
%token INVARSPEC_Token	"INVARSPEC"
%token FAIRNESS_Token	"FAIRNESS"
%token JUSTICE_Token	"JUSTICE"
%token COMPASSION_Token	"COMPASSION"
%token ISA_Token	"ISA"
%token ASSIGN_Token	"ASSIGN"
%token CONSTRAINT_Token	"CONSTRAINT"
%token SIMPWFF_Token	"SIMPWFF"
%token CTLWFF_Token	"CTLWFF"
%token LTLWFF_Token	"LTLWFF"
%token PSLWFF_Token	"PSLWFF"
%token COMPWFF_Token	"COMPWFF"
%token MIN_Token	"MIN"
%token MAX_Token	"MAX"
%token MIRROR_Token	"MIRROR"
%token PRED_Token	"PRED"
%token PREDICATES_Token	"PREDICATES"

%token process_Token	"process"
%token array_Token	"array"
%token of_Token		"of"
%token boolean_Token	"boolean"
%token integer_Token	"integer"
%token real_Token	"real"
%token word_Token	"word"
%token word1_Token	"word1"
%token bool_Token	"bool"
%token signed_Token	"signed"
%token unsigned_Token	"unsigned"
%token extend_Token	"extend"
%token resize_Token	"resize"
%token sizeof_Token	"sizeof"
%token uwconst_Token	"uwconst"
%token swconst_Token	"swconst"

%token EX_Token		"EX"
%token AX_Token		"AX"
%token EF_Token		"EF"
%token AF_Token		"AF"
%token EG_Token		"EG"
%token AG_Token		"AG"
%token E_Token		"E"
%token F_Token		"F"
%token O_Token		"O"
%token G_Token		"G"
%token H_Token		"H"
%token X_Token		"X"
%token Y_Token		"Y"
%token Z_Token		"Z"
%token A_Token		"A"
%token U_Token		"U"
%token S_Token		"S"
%token V_Token		"V"
%token T_Token		"T"
%token BU_Token		"BU"
%token EBF_Token	"EBF"
%token ABF_Token	"ABF"
%token EBG_Token	"EBG"
%token ABG_Token	"ABG"

%token case_Token	"case"
%token esac_Token	"esac"
%token mod_Token	"mod"
%token next_Token	"next"
%token init_Token	"init"
%token union_Token	"union"
%token in_Token		"in"
%token xor_Token	"xor"
%token xnor_Token	"xnor"
%token self_Token	"self"
%token TRUE_Token	"TRUE"
%token FALSE_Token	"FALSE"
%token count_Token	"count"
%token abs_Token	"abs"
%token max_Token	"max"
%token min_Token	"min"

/* Not in the NuSMV manual */
%token EXTERN_Token	"EXTERN"
%token switch_Token	"switch"
%token notin_Token	"notin"
%token R_Token		"R"

%token DOTDOT_Token   ".."
%token IMPLIES_Token  "->"
%token EQUIV_Token    "<->"
%token IF_Token       "?"
%token OR_Token       "|"
%token AND_Token      "&"
%token NOT_Token      "!"
%token DOT_Token      "."
%token PLUS_Token     "+"
%token MINUS_Token    "-"
%token EQUAL_Token    "="
%token LE_Token       "<="
%token GE_Token       ">="
%token LT_Token       "<"
%token GT_Token       ">"
%token NOTEQUAL_Token "!="
%token LTLT_Token     "<<"
%token GTGT_Token     ">>"

%token INC_Token
%token DEC_Token
%token BECOMES_Token  ":="
%token ADD_Token
%token SUB_Token

%token IDENTIFIER_Token   "identifier"
%token QIDENTIFIER_Token  "quoted identifier"
%token STRING_Token    "quoted string"
%token NUMBER_Token   "number"

/* operator precedence, low to high */
%right IMPLIES_Token
%left  EQUIV_Token
%left  IF_Token
%left  xor_Token xnor_Token
%left  OR_Token
%left  AND_Token
%left  NOT_Token
%left  EX_Token AX_Token EF_Token AF_Token EG_Token AG_Token E_Token A_Token U_Token R_Token V_Token F_Token G_Token H_Token O_Token S_Token T_Token X_Token Y_Token Z_Token EBF_Token ABF_Token EBG_Token ABG_Token
%left  EQUAL_Token NOTEQUAL_Token LT_Token GT_Token LE_Token GE_Token
%left  union_Token
%left  in_Token
%left  mod_Token /* Precedence from CMU SMV, different from NuSMV */
%left  LTLT_Token GTGT_Token
%left  PLUS_Token MINUS_Token
%left  TIMES_Token DIVIDE_Token
%left  COLONCOLON_Token
%left  UMINUS           /* supplies precedence for unary minus */
%left  DOT_Token

%%

start      : modules
           ;

modules    : module
           | modules module
           ;

module     : module_head module_body
           ;

module_name: IDENTIFIER_Token
           | STRING_Token
           ;

module_head: MODULE_Token module_name { new_module($2); }
           | MODULE_Token module_name { new_module($2); } '(' module_argument_list_opt ')'
           ;

module_body: /* optional */
           | module_body module_element
           ;
           
semi_opt   :    /* empty */
           | ';'
           ;

module_element:
             var_declaration
           | define_declaration
           | assign_constraint
           | trans_constraint
           | init_constraint
           | invar_constraint
           | fairness_constraint
           | ctl_specification
           | ltl_specification
           | EXTERN_Token extern_var semi_opt
           | EXTERN_Token
           ;

var_declaration:
             VAR_Token vardecls
           | VAR_Token
           ;

define_declaration:
             DEFINE_Token defines
           | DEFINE_Token
           ;

assign_constraint:
             ASSIGN_Token assignments
           | ASSIGN_Token
           ;

trans_constraint:
             TRANS_Token formula semi_opt { PARSER.module->add_trans(stack_expr($2), stack_expr($1).source_location()); }
           | TRANS_Token
           ;

init_constraint:
             INIT_Token formula semi_opt { PARSER.module->add_init(stack_expr($2), stack_expr($1).source_location()); }
           | INIT_Token
           ;

invar_constraint:
             INVAR_Token formula semi_opt { PARSER.module->add_invar(stack_expr($2), stack_expr($1).source_location()); }
           | INVAR_Token
           ;

fairness_constraint:
             FAIRNESS_Token formula semi_opt { PARSER.module->add_fairness(stack_expr($2), stack_expr($1).source_location()); }
           | FAIRNESS_Token
           ;

ctl_specification:
             SPEC_Token formula semi_opt
           {
             PARSER.module->add_ctlspec(
               stack_expr($2),
               stack_expr($1).source_location());
           }
           | SPEC_Token
           | CTLSPEC_Token formula semi_opt
           {
             PARSER.module->add_ctlspec(
               stack_expr($2),
               stack_expr($1).source_location());
           }
           | CTLSPEC_Token
           | SPEC_Token NAME_Token identifier BECOMES_Token formula semi_opt
           {
             PARSER.module->add_ctlspec(
               stack_expr($3).id(),
               stack_expr($5),
               stack_expr($1).source_location());
           }
           | CTLSPEC_Token NAME_Token identifier BECOMES_Token formula semi_opt
           {
             PARSER.module->add_ctlspec(
               stack_expr($3).id(),
               stack_expr($5),
               stack_expr($1).source_location());
           }
           ;

ltl_specification:
             LTLSPEC_Token formula semi_opt
           { 
             PARSER.module->add_ltlspec(stack_expr($2), stack_expr($1).source_location());
           }
           | LTLSPEC_Token           
           | LTLSPEC_Token NAME_Token identifier BECOMES_Token formula semi_opt
           { 
             PARSER.module->add_ltlspec(
               stack_expr($3).id(),
               stack_expr($5),
               stack_expr($1).source_location());
           }
           ;
 
extern_var : variable_identifier EQUAL_Token STRING_Token
           {
             const irep_idt &identifier=stack_expr($1).get(ID_identifier);
             smv_parse_treet::mc_vart &var=PARSER.module->vars[identifier];

             if(var.identifier!=irep_idt())
             {
               yyerror("variable `"+id2string(identifier)+"' already declared extern");
               YYERROR;
             }
             else
               var.identifier=stack_expr($3).id_string();
           }
           ;

vardecls   : vardecl
           | vardecls vardecl
           ;

module_argument: variable_identifier
           {
             const irep_idt &identifier=stack_expr($1).get(ID_identifier);
             smv_parse_treet::mc_vart &var=PARSER.module->vars[identifier];
             var.var_class=smv_parse_treet::mc_vart::ARGUMENT;
             PARSER.module->ports.push_back(identifier);
           }
           ;

module_argument_list: module_argument
           | module_argument_list ',' module_argument
           ;

module_argument_list_opt: /* empty */
           | module_argument_list
           ;

type_specifier:
             simple_type_specifier
           | module_type_specifier
           ;

simple_type_specifier:
             array_Token NUMBER_Token DOTDOT_Token NUMBER_Token of_Token simple_type_specifier
           {
             init($$, ID_array);
             int start=atoi(stack_expr($2).id().c_str());
             int end=atoi(stack_expr($4).id().c_str());

             if(end < start)
             {
               yyerror("array must end with number >= `"+std::to_string(start)+"'");
               YYERROR;
             }

             stack_type($$).set(ID_size, end-start+1);
             stack_type($$).set(ID_offset, start);
             stack_type($$).add_subtype()=stack_type($6);
           }
           | boolean_Token { init($$, ID_bool); }
           | word_Token '[' NUMBER_Token ']'
           {
             init($$, ID_unsignedbv);
             stack_type($$).set(ID_width, stack_expr($3).id());
           }
           | signed_Token word_Token '[' NUMBER_Token ']'
           {
             init($$, ID_signedbv);
             stack_type($$).set(ID_width, stack_expr($4).id());
           }
           | unsigned_Token word_Token '[' NUMBER_Token ']'
           {
             init($$, ID_unsignedbv);
             stack_type($$).set(ID_width, stack_expr($4).id());
           }
           | '{' enum_list '}' { $$=$2; }
           | NUMBER_Token DOTDOT_Token NUMBER_Token
           {
             init($$, ID_range);
             stack_type($$).set(ID_from, stack_expr($1));
             stack_type($$).set(ID_to, stack_expr($3));
           }
           ;

module_type_specifier:
             module_name
           {
             init($$, "submodule");
             stack_expr($$).set(ID_identifier,
                           smv_module_symbol(stack_expr($1).id_string()));
           }
           | module_name '(' formula_list ')'
           {
             init($$, "submodule");
             stack_expr($$).set(ID_identifier,
                           smv_module_symbol(stack_expr($1).id_string()));
             stack_expr($$).operands().swap(stack_expr($3).operands());
           }
           ;

enum_list  : enum_element
           {
             init($$, ID_enumeration);
             stack_expr($$).add(ID_elements).get_sub().push_back(irept(stack_expr($1).id()));
           }
           | enum_list ',' enum_element
           {
             $$=$1;
             stack_expr($$).add(ID_elements).get_sub().push_back(irept(stack_expr($3).id())); 
           }
           ;

enum_element: IDENTIFIER_Token
           {
             $$=$1;
             PARSER.module->enum_set.insert(stack_expr($1).id_string());
           }
           ;

vardecl    : variable_identifier ':' type_specifier ';'
{
  const irep_idt &identifier=stack_expr($1).get(ID_identifier);
  smv_parse_treet::mc_vart &var=PARSER.module->vars[identifier];

  switch(var.var_class)
  {
  case smv_parse_treet::mc_vart::UNKNOWN:
    var.type=(typet &)stack_expr($3);
    var.var_class=smv_parse_treet::mc_vart::DECLARED;
    break;

  case smv_parse_treet::mc_vart::DEFINED:
    yyerror("variable `"+id2string(identifier)+"' already defined");
    YYERROR;
    break;

  case smv_parse_treet::mc_vart::DECLARED:
    yyerror("variable `"+id2string(identifier)+"' already declared as variable");
    YYERROR;
    break;
  
  case smv_parse_treet::mc_vart::ARGUMENT:
    yyerror("variable `"+id2string(identifier)+"' already declared as argument");
    YYERROR;
    break;
  
  default:
    DATA_INVARIANT(false, "unexpected variable class");
  }
}
           ;

assignments: assignment
           | assignments assignment
           ;

assignment : assignment_head '(' assignment_var ')' BECOMES_Token formula ';'
           {
             if(stack_expr($1).id()==ID_smv_next)
             {
               PARSER.module->add_assign_next(
                 unary_exprt{ID_smv_next, std::move(stack_expr($3))},
                 std::move(stack_expr($6)));
             }
             else
               PARSER.module->add_assign_init(std::move(stack_expr($3)), std::move(stack_expr($6)));
           }
           | assignment_var BECOMES_Token formula ';'
           {
             const irep_idt &identifier=stack_expr($1).get(ID_identifier);
             smv_parse_treet::mc_vart &var=PARSER.module->vars[identifier];

             switch(var.var_class)
             {
             case smv_parse_treet::mc_vart::UNKNOWN:
               var.type.make_nil();
               var.var_class=smv_parse_treet::mc_vart::DEFINED;
               break;

             case smv_parse_treet::mc_vart::DECLARED:
               var.var_class=smv_parse_treet::mc_vart::DEFINED;
               break;

             case smv_parse_treet::mc_vart::DEFINED:
               yyerror("variable `"+id2string(identifier)+"' already defined");
               YYERROR;
               break;
             
             case smv_parse_treet::mc_vart::ARGUMENT:
               yyerror("variable `"+id2string(identifier)+"' already declared as argument");
               YYERROR;
               break;
             
             default:
               DATA_INVARIANT(false, "unexpected variable class");
             }

             PARSER.module->add_assign_current(std::move(stack_expr($1)), std::move(stack_expr($3)));
           }
           ;

assignment_var: variable_identifier
           ;

assignment_head: init_Token { init($$, ID_init); }
               | next_Token { init($$, ID_smv_next); }
               ;

defines:     define
           | defines define
           ;

define     : assignment_var BECOMES_Token formula ';'
           {
             const irep_idt &identifier=stack_expr($1).get(ID_identifier);
             smv_parse_treet::mc_vart &var=PARSER.module->vars[identifier];

             switch(var.var_class)
             {
             case smv_parse_treet::mc_vart::UNKNOWN:
               var.type.make_nil();
               var.var_class=smv_parse_treet::mc_vart::DEFINED;
               break;

             case smv_parse_treet::mc_vart::DECLARED:
               yyerror("variable `"+id2string(identifier)+"' already declared");
               YYERROR;
               break;

             case smv_parse_treet::mc_vart::DEFINED:
               yyerror("variable `"+id2string(identifier)+"' already defined");
               YYERROR;
               break;

             case smv_parse_treet::mc_vart::ARGUMENT:
               yyerror("variable `"+id2string(identifier)+"' already declared as argument");
               YYERROR;
               break;

             default:
               DATA_INVARIANT(false, "unexpected variable class");
             }

             PARSER.module->add_define(std::move(stack_expr($1)), std::move(stack_expr($3)));
           }
           ;

formula    : term
           ;

term       : variable_identifier
           | next_Token '(' term ')'  { init($$, ID_smv_next); mto($$, $3); }
           | '(' formula ')'          { $$=$2; }
           | '{' formula_list '}'     { $$=$2; stack_expr($$).id(ID_smv_set); }
           | INC_Token '(' term ')'   { init($$, "inc"); mto($$, $3); }
           | DEC_Token '(' term ')'   { init($$, "dec"); mto($$, $3); }
           | ADD_Token '(' term ',' term ')' { j_binary($$, $3, ID_plus, $5); }
           | SUB_Token '(' term ',' term ')' { init($$, ID_minus); mto($$, $3); mto($$, $5); }
           | NUMBER_Token             { init($$, ID_constant); stack_expr($$).set(ID_value, stack_expr($1).id()); stack_expr($$).type()=integer_typet(); }
           | TRUE_Token               { init($$, ID_constant); stack_expr($$).set(ID_value, ID_true); stack_expr($$).type()=typet(ID_bool); }
           | FALSE_Token              { init($$, ID_constant); stack_expr($$).set(ID_value, ID_false); stack_expr($$).type()=typet(ID_bool); }
           | case_Token cases esac_Token { $$=$2; }
           | term IF_Token term ':' term %prec IF_Token
                                      { init($$, ID_if); mto($$, $1); mto($$, $3); mto($$, $5); }
           | switch_Token '(' variable_identifier ')' '{' switches '}' { init($$, ID_switch); mto($$, $3); mto($$, $6); }
           | MINUS_Token term %prec UMINUS
                                      { init($$, ID_unary_minus); mto($$, $2); }
           | term mod_Token term      { binary($$, $1, ID_mod, $3); }
           | term GTGT_Token term     { binary($$, $1, ID_shr, $3); }
           | term LTLT_Token term     { binary($$, $1, ID_shl, $3); }
           | term COLONCOLON_Token term { binary($$, $1, ID_concatenation, $3); }
           | term TIMES_Token term    { binary($$, $1, ID_mult, $3); }
           | term DIVIDE_Token term   { binary($$, $1, ID_div, $3); }
           | term PLUS_Token term     { binary($$, $1, ID_plus, $3); }
           | term MINUS_Token term    { binary($$, $1, ID_minus, $3); }
           | term EQUIV_Token term    { binary($$, $1, ID_smv_iff, $3); }
           | term IMPLIES_Token term  { binary($$, $1, ID_implies, $3); }
           | term xor_Token term      { j_binary($$, $1, ID_xor, $3); }
           | term xnor_Token term     { binary($$, $1, ID_xnor, $3); }
           | term OR_Token term       { j_binary($$, $1, ID_or, $3); }
           | term AND_Token term      { j_binary($$, $1, ID_and, $3); }
           | NOT_Token term           { init($$, ID_not); mto($$, $2); }
           | term EQUAL_Token    term { binary($$, $1, ID_equal, $3); }
           | term NOTEQUAL_Token term { binary($$, $1, ID_notequal, $3); }
           | term LT_Token       term { binary($$, $1, ID_lt, $3); }
           | term LE_Token       term { binary($$, $1, ID_le, $3); }
           | term GT_Token       term { binary($$, $1, ID_gt, $3); }
           | term GE_Token       term { binary($$, $1, ID_ge, $3); }
           | term union_Token    term { binary($$, $1, ID_smv_union, $3); }
           | term in_Token       term { binary($$, $1, ID_smv_setin, $3); }
           | extend_Token '(' term ',' term ')' { binary($$, $3, ID_smv_extend, $5); }
           | resize_Token '(' term ',' term ')' { binary($$, $3, ID_smv_resize, $5); }
           | signed_Token '(' term ')' { init($$, ID_smv_signed_cast); mto($$, $3); }
           | sizeof_Token '(' term ')' { init($$, ID_smv_sizeof); mto($$, $3); }
           | swconst_Token '(' term ',' term ')' { binary($$, $3, ID_smv_swconst, $5); }
           | unsigned_Token '(' term ')' { init($$, ID_smv_unsigned_cast); mto($$, $3); }
           | uwconst_Token '(' term ',' term ')' { binary($$, $3, ID_smv_uwconst, $5); }
           /* CTL */
           | AX_Token  term           { init($$, ID_AX);  mto($$, $2); }
           | AF_Token  term           { init($$, ID_AF);  mto($$, $2); }
           | AG_Token  term           { init($$, ID_AG);  mto($$, $2); }
           | EX_Token  term           { init($$, ID_EX);  mto($$, $2); }
           | EF_Token  term           { init($$, ID_EF);  mto($$, $2); }
           | EG_Token  term           { init($$, ID_EG);  mto($$, $2); }
           | A_Token '[' term U_Token term ']' { binary($$, $3, ID_AU, $5); }
           | A_Token '[' term R_Token term ']' { binary($$, $3, ID_AR, $5); }
           | E_Token '[' term U_Token term ']' { binary($$, $3, ID_EU, $5); }
           | E_Token '[' term R_Token term ']' { binary($$, $3, ID_ER, $5); }
           /* LTL */
           | F_Token  term            { init($$, ID_F);  mto($$, $2); }
           | G_Token  term            { init($$, ID_G);  mto($$, $2); }
           | X_Token  term            { init($$, ID_X);  mto($$, $2); }
           | term U_Token term        { binary($$, $1, ID_U, $3); }
           | term R_Token term        { binary($$, $1, ID_R, $3); }
           | term V_Token term        { binary($$, $1, ID_R, $3); }
           /* LTL PAST */
           | Y_Token term             { $$ = $1; stack_expr($$).id(ID_smv_Y); mto($$, $2); }
           | Z_Token term             { $$ = $1; stack_expr($$).id(ID_smv_Z); mto($$, $2); }
           | H_Token term             { $$ = $1; stack_expr($$).id(ID_smv_H); mto($$, $2); }
           | H_Token bound term       { $$ = $1; stack_expr($$).id(ID_smv_bounded_H); mto($$, $3); }
           | O_Token term             { $$ = $1; stack_expr($$).id(ID_smv_O); mto($$, $2); }
           | O_Token bound term       { $$ = $1; stack_expr($$).id(ID_smv_bounded_O); mto($$, $3); }
           | term S_Token term        { $$ = $2; stack_expr($$).id(ID_smv_S); mto($$, $1); mto($$, $3); }
           | term T_Token term        { $$ = $2; stack_expr($$).id(ID_smv_T); mto($$, $1); mto($$, $3); }
           /* Real-time CTL */
           | EBF_Token range term     { $$ = $1; stack_expr($$).id(ID_smv_EBF); stack_expr($$).operands().swap(stack_expr($2).operands()); mto($$, $3); }
           | ABF_Token range term     { $$ = $1; stack_expr($$).id(ID_smv_ABF); stack_expr($$).operands().swap(stack_expr($2).operands()); mto($$, $3); }
           | EBG_Token range term     { $$ = $1; stack_expr($$).id(ID_smv_EBG); stack_expr($$).operands().swap(stack_expr($2).operands()); mto($$, $3); }
           | ABG_Token range term     { $$ = $1; stack_expr($$).id(ID_smv_ABG); stack_expr($$).operands().swap(stack_expr($2).operands()); mto($$, $3); }
           | A_Token '[' term BU_Token range term ']'
           {
             $$ = $1;
             stack_expr($$).id(ID_smv_ABU);
             mto($$, $3);
             stack_expr($$).add_to_operands(stack_expr($5).operands()[0]);
             stack_expr($$).add_to_operands(stack_expr($5).operands()[1]);
             mto($$, $6);
           }
           | E_Token '[' term BU_Token range term ']'
           {
             $$ = $1;
             stack_expr($$).id(ID_smv_EBU);
             mto($$, $3);
             stack_expr($$).add_to_operands(stack_expr($5).operands()[0]);
             stack_expr($$).add_to_operands(stack_expr($5).operands()[1]);
             mto($$, $6);
           }
           ;

bound      : '[' NUMBER_Token ',' NUMBER_Token ']'
           { init($$); mto($$, $2); mto($$, $4); }
           ;

range      : NUMBER_Token DOTDOT_Token NUMBER_Token
           { init($$); mto($$, $1); mto($$, $3); }
           ;

formula_list:
             formula { init($$); mto($$, $1); }
           | formula_list ',' formula { $$=$1; mto($$, $3); }
           ;

identifier : IDENTIFIER_Token
           | QIDENTIFIER_Token
           {
             // not supported by NuSMV
             init($$, std::string(stack_expr($1).id_string(), 1)); // remove backslash
           }
           ;

variable_identifier: complex_identifier
           {
             const irep_idt &id=stack_expr($1).id();

             bool is_enum=(PARSER.module->enum_set.find(id)!=
                           PARSER.module->enum_set.end());
             bool is_var=(PARSER.module->vars.find(id)!=
                          PARSER.module->vars.end());

             if(is_var && is_enum)
             {
               yyerror("identifier `"+id2string(id)+"' is ambiguous");
               YYERROR;
             }
             else if(is_enum)
             {
               init($$, ID_constant);
               stack_expr($$).type()=typet(ID_enumeration);
               stack_expr($$).set(ID_value, id);
             }
             else // not an enum, probably a variable
             {
               init($$, ID_symbol);
               stack_expr($$).set(ID_identifier, id);
               auto var_it = PARSER.module->vars.find(id);
               if(var_it!= PARSER.module->vars.end())
                 stack_expr($$).type()=var_it->second.type;
               //PARSER.module->vars[stack_expr($1).id()];
             }
           }
           | STRING_Token
           {
             const irep_idt &id=stack_expr($1).id();

             init($$, ID_symbol);
             stack_expr($$).set(ID_identifier, id);
             PARSER.module->vars[id];
           }
           ;

complex_identifier:
             identifier
           | complex_identifier DOT_Token QIDENTIFIER_Token
           {
             std::string id(stack_expr($1).id_string());
             id+=".";
             id+=std::string(stack_expr($3).id_string(), 1); // remove backslash
             init($$, id);
           }
           | complex_identifier DOT_Token IDENTIFIER_Token
           {
             std::string id(stack_expr($1).id_string());
             id+=".";
             id+=stack_expr($3).id_string();
             init($$, id);
           }
           | complex_identifier '[' NUMBER_Token ']'
           {
             std::string id(stack_expr($1).id_string());
             id+="[";
             id+=stack_expr($3).id_string();
             id+="]";
             init($$, id);
           }
           | complex_identifier '(' NUMBER_Token ')'
           {
             std::string id(stack_expr($1).id_string());
             id+="(";
             id+=stack_expr($3).id_string();
             id+=")";
             init($$, id);
           }
           ;

cases      :
           { init($$, "smv_cases"); }
           | cases case
           { $$=$1; mto($$, $2); }
           ;

case       : formula ':' formula ';'
           { binary($$, $1, ID_case, $3); }
           ;

switches   :
           { init($$, "switches"); }
           | switches switch
           { $$=$1; mto($$, $2); }
           ;

switch     : NUMBER_Token ':' term ';'
           { init($$, ID_switch); mto($$, $1); mto($$, $3); }
           ;

%%

int yysmverror(const std::string &error)
{
  PARSER.parse_error(error, yytext);
  return 0;
}

#undef yyerror

