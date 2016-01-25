%{

// Based on BNF Syntax at
// http://tams-www.informatik.uni-hamburg.de/vhdl/tools/grammar/vhdl93-bnf.html

#include <cstring>
#include <iostream>

#include <util/dstring.h>

#include "vhdl_parser.h"

#define PARSER vhdl_parser
#define YYSTYPE unsigned
#define YYSTYPE_IS_TRIVIAL 1

#define mto(x, y) stack(x).move_to_operands(stack(y))
#define mts(x, y) stack(x).move_to_sub((irept &)stack(y))

int yyvhdllex();
extern char *yyvhdltext;

/*******************************************************************\

Function: yyvhdlerror

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int yyvhdlerror(const char *error_str)
{
  PARSER.parse_error(error_str, yyvhdltext);
  return strlen(error_str)+1;
}

/*******************************************************************\

Function: init

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

inline static void init(exprt &expr)
{
  expr.clear();
  PARSER.set_source_location(expr);
}

/*******************************************************************\

Function: init

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

inline static void init(YYSTYPE &expr)
{
  newstack(expr);
  init(stack(expr));
}

/*******************************************************************\

Function: make_nil

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

inline static void make_nil(YYSTYPE &expr)
{
  newstack(expr);
  stack(expr).make_nil();
}

/*******************************************************************\

Function: init

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

inline static void init(YYSTYPE &expr, const irep_idt &id)
{
  init(expr);
  stack(expr).id(id);
}

%}

%right '='
%left ORL
%left ANDL
%left TOK_OR
%left TOK_XOR
%left TOK_AND
%left TOK_MOD
%left '<' '>' BIGEQ LESSEQ NOTEQ EQUAL
%left '+' '-' '&'
%left '*' '/'
%right UMINUS UPLUS NOTL TOK_NOT

%token TOK_ABS "ABS"
%token TOK_ACCESS "ACCESS" 
%token TOK_AFTER "AFTER" 
%token TOK_ALIAS "ALIAS" 
%token TOK_ALL "ALL" 
%token TOK_AND "AND" 
%token TOK_ARCHITECTURE "ARCHITECTURE" 
%token TOK_ARRAY "ARRAY" 
%token TOK_ASSERT "ASSERT" 
%token TOK_ATTRIBUTE "ATTRIBUTE" 
%token TOK_BEGIN "BEGIN" 
%token TOK_BLOCK "BLOCK" 
%token TOK_BODY "BODY" 
%token TOK_BUFFER "BUFFER" 
%token TOK_BUS "BUS" 
%token TOK_CASE "CASE" 
%token TOK_COMPONENT "COMPONENT" 
%token TOK_CONFIGURATION "CONFIGURATION" 
%token TOK_CONSTANT "CONSTANT" 
%token TOK_DISCONNENT "DISCONNENT" 
%token TOK_DOWNTO "DOWNTO" 
%token TOK_ELSE "ELSE" 
%token TOK_ELSIF "ELSIF" 
%token TOK_END "END" 
%token TOK_ENTITY "ENTITY" 
%token TOK_EXIT "EXIT" 
%token TOK_FILE "FILE" 
%token TOK_FOR "FOR" 
%token TOK_FUNCTION "FUNCTION" 
%token TOK_GENERATE "GENERATE" 
%token TOK_GENERIC "GENERIC" 
%token TOK_GROUP "GROUP" 
%token TOK_GUARDED "GUARDED" 
%token TOK_IF "IF" 
%token TOK_IMPURE "IMPURE" 
%token TOK_IN "IN" 
%token TOK_INERTIAL "INERTIAL" 
%token TOK_INOUT "INOUT" 
%token TOK_IS "IS" 
%token TOK_LABEL "LABEL" 
%token TOK_LIBRARY "LIBRARY" 
%token TOK_LINKAGE "LINKAGE" 
%token TOK_LITERAL "LITERAL" 
%token TOK_LOOP "LOOP" 
%token TOK_MAP "MAP" 
%token TOK_MOD "MOD" 
%token TOK_NAND "NAND" 
%token TOK_NEW "NEW" 
%token TOK_NEXT "NEXT" 
%token TOK_NOR "NOR" 
%token TOK_NOT "NOT" 
%token TOK_NULL "NULL" 
%token TOK_OF "OF" 
%token TOK_ON "ON" 
%token TOK_OPEN "OPEN" 
%token TOK_OR "OR" 
%token TOK_OTHERS "OTHERS" 
%token TOK_OUT "OUT" 
%token TOK_PACKAGE "PACKAGE" 
%token TOK_PORT "PORT" 
%token TOK_POSTPONED "POSTPONED" 
%token TOK_PROCEDURE "PROCEDURE" 
%token TOK_PROCESS "PROCESS" 
%token TOK_PROTECTED "PROTECTED"
%token TOK_PURE "PURE" 
%token TOK_RANGE "RANGE" 
%token TOK_RECORD "RECORD" 
%token TOK_REGISTER "REGISTER" 
%token TOK_REJECT "REJECT" 
%token TOK_REM "REM" 
%token TOK_REPORT "REPORT" 
%token TOK_RETURN "RETURN" 
%token TOK_ROL "ROL" 
%token TOK_ROR "ROR" 
%token TOK_SELECT "SELECT" 
%token TOK_SEVERITY "SEVERITY" 
%token TOK_SIGNAL "SIGNAL" 
%token TOK_SLA "SLA" 
%token TOK_SLL "SLL" 
%token TOK_SRA "SRA" 
%token TOK_SRL "SRL" 
%token TOK_SUBTYPE "SUBTYPE" 
%token TOK_THEN "THEN" 
%token TOK_TO "TO" 
%token TOK_TRANSPORT "TRANSPORT" 
%token TOK_TYPE "TYPE" 
%token TOK_UNAFFECTED "UNAFFECTED" 
%token TOK_UNITS "UNITS" 
%token TOK_UNTIL "UNTIL" 
%token TOK_USE "USE" 
%token TOK_VARIABLE "VARIABLE" 
%token TOK_WAIT "WAIT" 
%token TOK_WHEN "WHEN" 
%token TOK_WHILE "WHILE" 
%token TOK_WITH "WITH" 
%token TOK_XNOR "XNOR" 
%token TOK_XOR "XOR"

%token TOK_NATURAL
%token TOK_BASED_INTEGER
%token TOK_STRING
%token TOK_BIT_STRING
%token TOK_CHAR
%token TOK_IDENTIFIER

/* the usual "dangling if" */
/* %expect 1 */

%%

design_file:
         /* nothing */
       | design_file design_unit
       ;

design_unit:
         context_clause library_unit
       | library_unit
       ;

context_clause:
         context_item
       | context_clause context_item
       ;

context_item:
         library_clause
       | use_clause
       ;
       
use_clause:
         TOK_USE name_list ';'
       {
       }
       ;

name_list:
         name
       {
         init($$);
         mts($$, $1);
       }
       | name_list ',' name
       {
         $$=$1;
         mts($$, $3);
       }
       ;

name:
         TOK_IDENTIFIER
       {
         $$=$1;
         irep_idt id=stack($$).id();
         stack($$).id(ID_symbol);
         stack($$).set(ID_identifier, id);
       }
       | selected_name
       ;
       
selected_name:
         name '.' TOK_IDENTIFIER
       {
         init($$, ID_member);
         stack($$).move_to_operands(stack($1));
         stack($$).set(ID_component_name, stack($3).id());
       }
       | name '.' TOK_ALL
       {
         init($$, ID_all);
         stack($$).move_to_operands(stack($1));
       }
       ;
       
library_clause:
         TOK_LIBRARY name_list ';'
       ;

library_unit:
         primary_unit
       | secondary_unit
       ;

primary_unit:
         entity_declaration
       | package_declaration
       ;

package_declaration:
         TOK_PACKAGE name TOK_IS package_declarative_part TOK_END ';'
       ;
       
package_declarative_part:
       ;

secondary_unit:
         architecture
       | package
       ;

package:
         TOK_PACKAGE TOK_BODY name TOK_IS package_body_declarative_part TOK_END ';'
       ;

package_body_declarative_part:
       ;

entity_declaration:
         TOK_ENTITY name TOK_IS TOK_END name_opt ';'
       {
         //PARSER.new_entity();
       }
       | TOK_ENTITY name TOK_IS TOK_PORT '(' port_list ')' ';' TOK_END name_opt ';'
       {
         //PARSER.new_entity();
       }
       | TOK_ENTITY name TOK_IS TOK_GENERIC '(' generic_list ')' ';'
         TOK_PORT '(' port_list ')' ';' TOK_END name_opt ';'
       {
       }
       ;

generic_list:
         generic
       {
         init($$);
         mts($$, $1);
       }
       | generic_list ';' generic
       {
         $$=$1;
         mts($$, $3);
       }
       ;

generic:
         s_list ':' type ':' '=' expr
       {
       }
       | s_list ':' type
       {
       }
       ;

port_list:
         port
       {
         init($$);
         mts($$, $1);
       }
       | port_list ';' port
       {
         $$=$1;
         mts($$, $3);
       }
       ;

port:
         s_list ':' dir type
       {
         init($$, ID_port);
       }
       ;

dir:
         TOK_IN
       {
         init($$, ID_input);
       }
       | TOK_OUT
       {
         init($$, ID_output);
       }
       ;

type:  
         name '(' expr updown expr ')'
       {
       }
       | name '(' expr ')'
       {
       }
       | name '(' name '\'' TOK_RANGE ')'
       {
       }
       | name '(' name '\'' TOK_IDENTIFIER ')'
       {
         // relevant for id'event
       }
       | name 
       | '(' enumeration_literal_list ')'
       {
         init($$, ID_enumeration);
       }
       | TOK_RANGE expr updown expr
       {
         init($$, ID_range);
       }
       | TOK_ARRAY '(' index_constraint_list ')' TOK_OF type
       {
         init($$, ID_array);
       }
       | TOK_RECORD element_declaration_list TOK_END TOK_RECORD name_opt
       {
         init($$, ID_struct);
       }
       | TOK_ACCESS type
       {
         init($$, ID_reference);
         stack_type($$).subtype()=stack_type($2);
       }
       | TOK_TYPE TOK_IDENTIFIER
       {
         init($$);
       }
       | TOK_FILE TOK_OF type
       {
         init($$);
       }
       | TOK_PROTECTED TOK_END TOK_PROTECTED
       ;
       
element_declaration_list:
         element_declaration
       {
         init($$);
         mts($$, $1);
       }
       | element_declaration_list element_declaration
       {
         $$=$1;
         mts($$, $2);
       }
       ;

element_declaration:
         identifier_list ':' type ';'
       ;

identifier_list:
         TOK_IDENTIFIER
       {
         init($$);
         mts($$, $1);
       }
       | identifier_list TOK_IDENTIFIER
       {
         $$=$1;
         mts($$, $2);
       }
       ;

index_constraint_list:
         index_constraint
       | index_constraint_list ',' index_constraint
       ;
       
index_constraint:
         name 
       | name '(' name '\'' TOK_RANGE ')'
       {
       }
       | expr updown expr
       ;

enumeration_literal_list:
         enumeration_literal
       {
         init($$);
         mts($$, $1);
       }
       | enumeration_literal_list ',' enumeration_literal
       {
         $$=$1;
         mts($$, $3);
       }
       ;

enumeration_literal:
         TOK_IDENTIFIER
       | TOK_CHAR
       ;

updown: 
         TOK_DOWNTO
       {
       }
       | TOK_TO
       {
       }
       ;

architecture:
         TOK_ARCHITECTURE name TOK_OF name TOK_IS architecture_decl_list
         TOK_BEGIN architecture_body TOK_END name_opt ';'
       {
       }
       ;

architecture_decl_list:
         /* Empty */
       {
         init($$);
       }
       | architecture_decl_list architecture_decl
       {
         $$=$1;
         mts($$, $2);
       }
       ;

architecture_decl:
         TOK_SIGNAL s_list ':' type ';'
       {
       }
       | TOK_CONSTANT name ':' type ':' '=' expr ';'
       {
       }
       | TOK_TYPE name TOK_IS '(' s_list ')' ';'
       {
       }
       | TOK_COMPONENT name TOK_PORT
         '(' port_list ')' ';' TOK_END TOK_COMPONENT ';'
       {
       }
       | TOK_COMPONENT name TOK_GENERIC '(' generic_list ')' ';' 
         TOK_PORT '(' port_list ')' ';' TOK_END TOK_COMPONENT ';'
       {
       }
       ;

s_list:
         name
       {
         init($$);
         mts($$, $1);
       }
       | s_list ',' name
       {
         $$=$1;
         mts($$, $3);
       }
       ;

architecture_body:
         /* Empty */
       {
         init($$);
       }
       | architecture_body architecture_item
       {
         $$=$1;
         mto($$, $2);
       }
       ;

architecture_item:
         signal '<' '=' sigvalue
       {
       }
       | TOK_WITH expr TOK_SELECT signal '<' '=' with_list ';'
       {
       }
       | name ':' name TOK_PORT TOK_MAP '(' map_list ')' ';'
       {
       }
       | name ':' name TOK_GENERIC TOK_MAP '(' generic_map_list ')'
         TOK_PORT TOK_MAP '(' map_list ')' ';'
       {
       }
       | label_opt TOK_PROCESS '(' signal_list ')' process_decl_list
         TOK_BEGIN process_body TOK_END
         TOK_PROCESS name_opt ';'
       {
       }
       | label_opt TOK_PROCESS
         TOK_BEGIN process_body TOK_END
         TOK_PROCESS name_opt ';'
       {
       }
       | label_opt TOK_IF conditional_expr TOK_GENERATE architecture_body TOK_END TOK_GENERATE name_opt ';'
       {
       }
       | label_opt TOK_FOR signal TOK_IN expr TOK_TO expr TOK_GENERATE architecture_body TOK_END TOK_GENERATE name_opt ';'
       {
       }
       | label_opt TOK_FOR signal TOK_IN expr TOK_DOWNTO expr TOK_GENERATE architecture_body TOK_END TOK_GENERATE name_opt ';'
       {
       }
       ;

name_opt:
         /* Empty */
       {
         init($$, ID_nil);
       }
       | name
       ;

label_opt:
         /* Empty */
       {
         init($$, ID_nil);
       }
       | name ':'
       {
         $$=$1;
       }
       ;
       
with_list:
         with_item_list
       {
       }
       | with_item_list ',' expr delay_opt TOK_WHEN TOK_OTHERS
       {
       }
       | expr delay_opt TOK_WHEN TOK_OTHERS
       {
       }
       ;

with_item_list:
         with_item
       {
         init($$);
         mto($$, $1);
       }
       | with_item_list ',' with_item
       {
         init($$);
         mto($$, $3);
       }
       ;

with_item: 
         expr delay_opt TOK_WHEN with_value_list
       {
       }
       ;

process_decl_list:
         /* Empty */
       {
         init($$);
       }
       | process_decl_list process_decl
       {
         $$=$1;
         mts($$, $2);
       }
       ;

process_decl:
         TOK_VARIABLE s_list ':' type ';'
       {
       }
       | TOK_VARIABLE s_list ':' type ':' '=' expr ';'
       {
       }
       ;

process_body:
         /* Empty */
       {
         init($$);
       }
       | process_body process_item
       {
         $$=$1;
         mto($$, $2);
       }
       ;

process_item:
         signal ':' '=' expr ';'
       {
         init($$, ID_code);
         stack($$).set(ID_statement, ID_assign);
         stack($$).move_to_operands(stack($1), stack($4));
       }
       | signal '<' '=' sigvalue
       {
       }
       | TOK_IF conditional_expr TOK_THEN process_body elsepart TOK_END TOK_IF ';'
       {
         init($$, ID_code);
         stack($$).set(ID_statement, ID_ifthenelse);
         stack($$).move_to_operands(stack($2), stack($4), stack($5));
       }
       | TOK_FOR signal TOK_IN expr TOK_TO expr TOK_LOOP process_body TOK_END TOK_LOOP ';'
       {
       }
       | TOK_FOR signal TOK_IN expr TOK_DOWNTO expr TOK_LOOP process_body TOK_END TOK_LOOP ';'
       {
       }
       | TOK_CASE expr TOK_IS cases TOK_END TOK_CASE ';'
       {
       }
       | TOK_EXIT ';'
       {
       }
       | TOK_NULL ';'
       {
       }
       ;

elsepart:
         /* Empty */
       {
         init($$, ID_nil);
       }
       | TOK_ELSIF conditional_expr TOK_THEN process_body elsepart
       {
         init($$, ID_code);
         stack($$).set(ID_statement, ID_ifthenelse);
         stack($$).move_to_operands(stack($2), stack($4), stack($5));
       }
       | TOK_ELSE process_body
       {
         $$=$2;
       }
       ;

cases: 
         TOK_WHEN with_value_list '=' '>' process_body cases
       {
       }
       | TOK_WHEN TOK_OTHERS '=' '>' process_body
       {
       }
       ;

with_value_list:
         with_value
       {
         init($$);
         mts($$, $1);
       }
       | with_value_list '|' with_value
       {
         $$=$1;
         mts($$, $3);
       }
       ;

with_value: 
         TOK_STRING
       | name
       ;

signal_list:
         signal
       {
         init($$);
         mts($$, $1);
       }
       | signal_list ',' signal
       {
         $$=$1;
         mts($$, $3);
       }
       ;

sigvalue:
         expr delay_opt ';'
       {
         $$=$1;
       }
       | expr delay_opt TOK_WHEN conditional_expr ';'
       {
         init($$, ID_when);
         stack($$).move_to_operands(stack($1), stack($4));
       }
       | expr delay_opt TOK_WHEN conditional_expr TOK_ELSE sigvalue
       {
         init($$, ID_when);
         stack($$).move_to_operands(stack($1), stack($4), stack($6));
       }
       ;

delay_opt:
         /* empty */
       {
       }
       | TOK_AFTER TOK_NATURAL name
       {
       }
       ;

map_list:
         map_item
       {
         init($$);
         mts($$, $1);
       }
       | map_item ',' map_list
       {
         $$=$1;
         mts($$, $3);
       }
       ;

map_item: 
         signal
       | name '=' '>' signal
       {
       }
       ;

generic_map_list:
         generic_map_item
       {
         init($$);
         mts($$, $1);
       }
       | generic_map_item ',' generic_map_list
       {
         $$=$1;
         mts($$, $3);
       }
       ;

generic_map_item:
         name '=' '>' expr
       {
       }
       ;

signal:
         name
       | name '(' expr updown expr ')'
       {
         init($$, ID_extractbits);
         stack($$).move_to_operands(stack($1), stack($3), stack($5));
       }
       | name '(' name '\'' TOK_RANGE ')'
       {
         init($$, ID_extractbits);
       }
       ;

choice:
        
         TOK_OTHERS
       ;

choices:
         choice
       | choices '|' choice
       ;

element_association:
         choices '=' '>' expr
       ;

element_association_list:
         element_association
       | element_association_list ',' element_association
       ;

/* Expressions */
expr:
         signal
       | TOK_STRING 
       {
       }
       | TOK_BIT_STRING 
       {
       }
       | TOK_CHAR
       {
       }
       | TOK_NATURAL
       {
       }
       | TOK_NATURAL TOK_BASED_INTEGER
       {
       }
       | '(' element_association_list ')'
       {
       }
       | expr '&' expr
       { // Vector chaining
         init($$, ID_concatenation);
         stack($$).move_to_operands(stack($1), stack($3));
       }
       | '-' expr %prec UMINUS
       {
         init($$, ID_unary_minus);
         mto($$, $2);
       }
       | '+' expr %prec UPLUS
       {
         init($$, ID_unary_plus);
         mto($$, $2);
       }
       | expr '+' expr
       {
         init($$, ID_plus);
         stack($$).move_to_operands(stack($1), stack($3));
       }
       | expr '-' expr
       {
         init($$, ID_minus);
         stack($$).move_to_operands(stack($1), stack($3));
       }
       | expr '*' expr
       {
         init($$, ID_mult);
         stack($$).move_to_operands(stack($1), stack($3));
       }
       | expr '/' expr
       {
         init($$, ID_div);
         stack($$).move_to_operands(stack($1), stack($3));
       }
       | expr TOK_MOD expr
       {
         init($$, ID_mod);
         stack($$).move_to_operands(stack($1), stack($3));
       }
       | TOK_NOT expr
       {
         init($$, ID_not);
         mto($$, $2);
       }
       | expr TOK_AND expr
       {
         init($$, ID_and);
         stack($$).move_to_operands(stack($1), stack($3));
       }
       | expr TOK_OR expr
       {
         init($$, ID_or);
         stack($$).move_to_operands(stack($1), stack($3));
       }
       | expr TOK_XOR expr
       {
         init($$, ID_xor);
         stack($$).move_to_operands(stack($1), stack($3));
       }
       | name '(' expr_list ')'
       {
         init($$, ID_side_effect);
         stack($$).set(ID_statement, ID_function_call);
         stack($$).add(ID_operands).get_sub().swap(stack($3).get_sub());
       }
       | '(' expr ')'
       {
         $$=$2;
       }
       ;

expr_list:
         expr
       {
         init($$);
         mts($$, $1);
       }
       | expr_list ',' expr
       {
         $$=$1;
         mts($$, $3);
       }
       ;

conditional_expr: 
         comparison 
       | '(' conditional_expr ')'
       {
         $$=$2;
       }
       | conditional_expr TOK_AND conditional_expr %prec ANDL
       {
         init($$, ID_and);
         stack($$).move_to_operands(stack($1), stack($3));
       }
       | conditional_expr TOK_OR conditional_expr %prec ORL
       {
         init($$, ID_or);
         stack($$).move_to_operands(stack($1), stack($3));
       }
       | TOK_NOT conditional_expr %prec NOTL
       {
         init($$, ID_not);
         mto($$, $2);
       }
       ;

comparison:
         expr '=' expr %prec EQUAL
       {
         init($$, ID_equal);
         stack($$).move_to_operands(stack($1), stack($3));
       }
       | expr '>' expr
       {
         init($$, ID_gt);
         stack($$).move_to_operands(stack($1), stack($3));
       }
       | expr '>' '=' expr %prec BIGEQ
       {
         init($$, ID_ge);
         stack($$).move_to_operands(stack($1), stack($4));
       }
       | expr '<' expr
       {
         init($$, ID_lt);
         stack($$).move_to_operands(stack($1), stack($3));
       }
       | expr '<' '=' expr %prec LESSEQ
       {
         init($$, ID_le);
         stack($$).move_to_operands(stack($1), stack($4));
       }
       | expr '/' '=' expr %prec NOTEQ
       {
         init($$, ID_notequal);
         stack($$).move_to_operands(stack($1), stack($4));
       }
       ;
