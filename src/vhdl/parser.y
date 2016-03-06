%{

// Based on BNF Syntax at
// http://tams-www.informatik.uni-hamburg.de/vhdl/tools/grammar/vhdl93-bnf.html

#include <cstring>
#include <iostream>

#include <util/dstring.h>

#include "vhdl_parser.h"

#define PARSER vhdl_parser
#define YYSTYPE vhdl_parsert::yystypet

#undef stack
#undef stack_type
#define stack(x) (PARSER.stack[x.stack_index])
#define stack_type(x) (static_cast<typet &>(static_cast<irept &>(PARSER.stack[x.stack_index])))

#define mto(x, y) stack(x).move_to_operands(stack(y))
#define mts(x, y) stack(x).move_to_sub(stack(y))

int yyvhdllex();
extern char *yyvhdltext;

/*******************************************************************\

Function: yyvhdlerror

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

extern YYSTYPE yyvhdllval;

int yyvhdlerror(const char *error_str)
{
  std::string tmp=error_str;
  if(yyvhdltext[0]!=0)
  {
    tmp+=" before `";
    tmp+=yyvhdltext;
    tmp+='\'';
  }
    
  source_locationt source_location;
  source_location.set_column(yyvhdllval.column);
  source_location.set_line(yyvhdllval.line);
  source_location.set_file(yyvhdllval.file);

  PARSER.print(1, tmp, -1, source_location);
                  
  return strlen(error_str)+1;
}

/*******************************************************************\

Function: init

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

inline static void init(YYSTYPE &expr)
{
  newstack(expr.stack_index);
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

%{
// http://www.csee.umbc.edu/portal/help/VHDL/operator.html
%}

%left TOK_OR TOK_NOR TOK_XOR TOK_XNOR TOK_AND TOK_NAND
%left '=' TOK_NE '<' '>' TOK_GE TOK_LE
%left TOK_SLL TOK_SRL TOK_SLA TOK_SRA TOK_ROL TOK_ROR
%left '+' '-' '&'
%right UMINUS UPLUS
%left TOK_MOD '*' '/'
%right TOK_DOUBLE_STAR TOK_ABS TOK_NOT

%token TOK_ARROW "=>"
%token TOK_DOUBLE_STAR "**"
%token TOK_ASSIGN ":="
%token TOK_NE "/="
%token TOK_GE ">="
%token TOK_LE "<="
%token TOK_LEFT_LABEL_BRACKET "<<"
%token TOK_RIGHT_LABEL_BRACKET ">>"
%token TOK_BOX "<>"

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
         init($$, ID_symbol);
         $1.set_location(stack($$));
         stack($$).set(ID_identifier, $1.text);
       }
       | selected_name
       | name '\'' TOK_IDENTIFIER
       ;
       
selected_name:
         name '.' TOK_IDENTIFIER
       {
         init($$, ID_member);
         mto($$, $1);
         $2.set_location(stack($$));
         stack($$).set(ID_component_name, $3.text);
       }
       | name '.' TOK_ALL
       {
         init($$, ID_all);
         $2.set_location(stack($$));
         mto($$, $1);
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
         TOK_PACKAGE name TOK_IS package_declarative_part TOK_END name_opt ';'
       {
         vhdl_parse_treet::itemt &a=PARSER.new_package_item();
         $1.set_location(a);
         a.set_name(stack($2));
         a.set(ID_decl, stack($4));
       }
       ;
       
package_declarative_part:
         /* Empty */
       {
         init($$);
       }
       | package_declarative_part package_declarative_item
       {
         $$=$1;
         mts($$, $2);
       }
       ;
       
package_declarative_item:
         TOK_CONSTANT name ':' type ':' '=' expr ';'
       {
         init($$, ID_constant);
         $1.set_location(stack($$));
         mts($$, $2);
         mts($$, $7);
         stack($$).type()=stack_type($4);
       }
       | TOK_TYPE name TOK_IS type physical_units_opt ';'
       {
         init($$, ID_enumeration);
         $1.set_location(stack($$));
         mts($$, $2);
         mts($$, $5);
       }
       | TOK_SUBTYPE name TOK_IS name ';'
       {
         init($$, "subtype");
         $1.set_location(stack($$));
         mts($$, $2);
         mts($$, $4);
       }
       | TOK_SUBTYPE name TOK_IS name TOK_RANGE expr updown expr ';'
       {
         init($$, "subtype");
         $1.set_location(stack($$));
         mts($$, $2);
         mts($$, $4);
       }
       | TOK_ATTRIBUTE name ':' type ';'
       {
         init($$, "attribute");
         $1.set_location(stack($$));
         mts($$, $2);
         mts($$, $4);
       }
       ;

physical_units_opt:
         /* Empty */
       {
         init($$);
       }
       | TOK_UNITS name ';' secondary_physical_units TOK_END TOK_UNITS name_opt
       {
         init($$);
       }
       ;

secondary_physical_units:
         /* Empty */
       {
         init($$);
       }
       | secondary_physical_units name '=' TOK_NATURAL name ';'
       {
       }
       ;
       
secondary_unit:
         architecture
       | package
       ;

package:
         TOK_PACKAGE TOK_BODY name TOK_IS package_body_declarative_part TOK_END ';'
       {
       }
       ;

package_body_declarative_part:
       ;

entity_declaration:
         TOK_ENTITY name TOK_IS TOK_END name_opt ';'
       {
         vhdl_parse_treet::itemt &e=PARSER.new_entity_item();
         e.set_name(stack($2));
       }
       | TOK_ENTITY name TOK_IS TOK_PORT '(' port_list ')' ';' TOK_END name_opt ';'
       {
         vhdl_parse_treet::itemt &e=PARSER.new_entity_item();
         e.set_name(stack($2));
       }
       | TOK_ENTITY name TOK_IS TOK_GENERIC '(' generic_list ')' ';'
         TOK_PORT '(' port_list ')' ';' TOK_END name_opt ';'
       {
         vhdl_parse_treet::itemt &e=PARSER.new_entity_item();
         e.set_name(stack($2));
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
         name
       | TOK_CHAR
       {
         init($$, ID_constant);
         $1.set_location(stack($$));
         stack($$).set(ID_type, ID_char);
         stack($$).set(ID_value, $1.text);
       }
       ;

updown: 
         TOK_DOWNTO
       {
         init($$, "downto");
       }
       | TOK_TO
       {
         init($$, "to");
       }
       ;

architecture:
         TOK_ARCHITECTURE name TOK_OF name TOK_IS architecture_decl_list
         TOK_BEGIN architecture_body TOK_END name_opt ';'
       {
         vhdl_parse_treet::itemt &a=PARSER.new_architecture_item();
         $1.set_location(a);
         a.set_name(stack($2));
         a.set(ID_entity, stack($4));
         a.set(ID_decl, stack($6));
         a.set(ID_body, stack($8));
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
         init($$, ID_signal);
         $1.set_location(stack($$));
         stack($$).get_sub().swap(stack($2).get_sub());
         stack($$).type()=stack_type($4);
       }
       | TOK_CONSTANT name ':' type ':' '=' expr ';'
       {
         init($$, ID_constant);
         $1.set_location(stack($$));
         mts($$, $2);
         mts($$, $7);
         stack($$).type()=stack_type($4);
       }
       | TOK_TYPE name TOK_IS '(' enumeration_literal_list ')' ';'
       {
         init($$, ID_enumeration);
         $1.set_location(stack($$));
         mts($$, $2);
         mts($$, $5);
       }
       | TOK_COMPONENT name TOK_PORT
         '(' port_list ')' ';' TOK_END TOK_COMPONENT ';'
       {
         init($$, ID_component);
       }
       | TOK_COMPONENT name TOK_GENERIC '(' generic_list ')' ';' 
         TOK_PORT '(' port_list ')' ';' TOK_END TOK_COMPONENT ';'
       {
         init($$, ID_component);
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
         init($$, ID_body);
       }
       | architecture_body architecture_item
       {
         $$=$1;
         mto($$, $2);
       }
       ;

architecture_item:
         signal TOK_LE sigvalue
       {
         init($$, ID_continuous_assign);
         $2.set_location(stack($$));
         mto($$, $1);
         mto($$, $3);
       }
       | TOK_WITH expr TOK_SELECT signal TOK_LE with_list ';'
       {
         $$=$1;
       }
       | name ':' name TOK_PORT TOK_MAP '(' map_list ')' ';'
       {
         $$=$5;
       }
       | name ':' name TOK_GENERIC TOK_MAP '(' generic_map_list ')'
         TOK_PORT TOK_MAP '(' map_list ')' ';'
       {
         $$=$5;
       }
       | label_opt TOK_PROCESS '(' signal_list ')' process_decl_list
         TOK_BEGIN process_body TOK_END
         TOK_PROCESS name_opt ';'
       {
         init($$, ID_process);
         $2.set_location(stack($$));
         stack($$).operands().swap(stack($8).operands());
       }
       | label_opt TOK_PROCESS
         TOK_BEGIN process_body TOK_END
         TOK_PROCESS name_opt ';'
       {
         init($$, ID_process);
         $2.set_location(stack($$));
         stack($$).operands().swap(stack($4).operands());
       }
       | label_opt TOK_IF expr TOK_GENERATE architecture_body TOK_END TOK_GENERATE name_opt ';'
       {
         init($$, ID_generate_if);
         $2.set_location(stack($$));
         mto($$, $3);
         mto($$, $5);
       }
       | label_opt TOK_FOR signal TOK_IN expr TOK_TO expr TOK_GENERATE architecture_body TOK_END TOK_GENERATE name_opt ';'
       {
         init($$, ID_generate_for);
         $2.set_location(stack($$));
         mto($$, $3);
         mto($$, $5);
         mto($$, $7);
         mto($$, $9);
       }
       | label_opt TOK_FOR signal TOK_IN expr TOK_DOWNTO expr TOK_GENERATE architecture_body TOK_END TOK_GENERATE name_opt ';'
       {
         init($$, ID_generate_for);
         $2.set_location(stack($$));
         mto($$, $3);
         mto($$, $5);
         mto($$, $7);
         mto($$, $9);
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
         signal TOK_ASSIGN expr ';'
       {
         init($$, ID_code);
         $2.set_location(stack($$));
         stack($$).set(ID_statement, ID_assign);
         mto($$, $1);
         mto($$, $3);
       }
       | signal TOK_LE sigvalue
       {
         init($$, ID_code);
         $2.set_location(stack($$));
         stack($$).set(ID_statement, ID_continuous_assign);
         mto($$, $1);
         mto($$, $3);
       }
       | TOK_IF expr TOK_THEN process_body elsepart TOK_END TOK_IF ';'
       {
         init($$, ID_code);
         $1.set_location(stack($$));
         stack($$).set(ID_statement, ID_ifthenelse);
         stack($$).move_to_operands(stack($2), stack($4), stack($5));
       }
       | TOK_FOR signal TOK_IN expr TOK_TO expr TOK_LOOP process_body TOK_END TOK_LOOP ';'
       {
         init($$, ID_code);
         $1.set_location(stack($$));
         stack($$).set(ID_statement, ID_for);
         mto($$, $2);
         mto($$, $4);
         mto($$, $6);
         mto($$, $8);
       }
       | TOK_FOR signal TOK_IN expr TOK_DOWNTO expr TOK_LOOP process_body TOK_END TOK_LOOP ';'
       {
         init($$, ID_code);
         $1.set_location(stack($$));
         stack($$).set(ID_statement, ID_for);
         mto($$, $2);
         mto($$, $4);
         mto($$, $6);
         mto($$, $8);
       }
       | TOK_CASE expr TOK_IS cases TOK_END TOK_CASE ';'
       {
         init($$, ID_code);
         $1.set_location(stack($$));
         stack($$).set(ID_statement, ID_switch_case);
       }
       | TOK_EXIT ';'
       {
         init($$, ID_code);
         $1.set_location(stack($$));
         stack($$).set(ID_statement, "exit");
       }
       | TOK_NULL ';'
       {
       }
       | label_opt TOK_ASSERT expr assert_report_opt assert_severity_opt ';'
       {
         init($$, ID_code); $2.set_location(stack($$));
         stack($$).set(ID_statement, ID_assert);
         mto($$, $3);
         mto($$, $4);
         mto($$, $5);
       }
       ;

assert_report_opt:
         /* Empty */
       {
         init($$, ID_nil);
       }
       | TOK_REPORT expr
       {
         $$=$2;
       }
       ;

assert_severity_opt:
         /* Empty */
       {
         init($$, ID_nil);
       }
       | TOK_SEVERITY expr
       {
         $$=$2;
       }
       ;

elsepart:
         /* Empty */
       {
         init($$, ID_nil);
       }
       | TOK_ELSIF expr TOK_THEN process_body elsepart
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
         init($$, ID_when);
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
       | expr delay_opt TOK_WHEN expr ';'
       {
         init($$, ID_when);
         stack($$).move_to_operands(stack($1), stack($4));
       }
       | expr delay_opt TOK_WHEN expr TOK_ELSE sigvalue
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
         choices TOK_ARROW expr
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
         init($$, ID_constant);
         $1.set_location(stack($$));
         stack($$).set(ID_type, ID_string);
         stack($$).set(ID_value, $1.text);
       }
       | TOK_BIT_STRING 
       {
         init($$, ID_constant);
         $1.set_location(stack($$));
         stack($$).set(ID_type, ID_string);
         stack($$).set(ID_value, $1.text);
       }
       | TOK_CHAR
       {
         init($$, ID_constant);
         $1.set_location(stack($$));
         stack($$).set(ID_type, ID_char);
         stack($$).set(ID_value, $1.text);
       }
       | TOK_NATURAL
       {
         init($$, ID_constant);
         $1.set_location(stack($$));
         stack($$).set(ID_type, ID_natural);
         stack($$).set(ID_value, $1.text);
       }
       | TOK_NATURAL name
       {
         init($$, ID_constant);
         $1.set_location(stack($$));
         stack($$).set(ID_type, ID_natural);
         stack($$).set(ID_value, $1.text);
         // the name is a unit
       }
       | TOK_NATURAL TOK_BASED_INTEGER
       {
         init($$, ID_constant);
         $1.set_location(stack($$));
         stack($$).set(ID_type, ID_natural);
         stack($$).set(ID_value, $1.text);
       }
       | '(' element_association_list ')'
       {
       }
       | expr '&' expr
       { // Vector chaining
         init($$, ID_concatenation);
         $2.set_location(stack($$));
         stack($$).move_to_operands(stack($1), stack($3));
       }
       | '-' expr %prec UMINUS
       {
         init($$, ID_unary_minus);
         $1.set_location(stack($$));
         mto($$, $2);
       }
       | '+' expr %prec UPLUS
       {
         init($$, ID_unary_plus);
         $1.set_location(stack($$));
         mto($$, $2);
       }
       | expr '+' expr
       {
         init($$, ID_plus);
         $2.set_location(stack($$));
         stack($$).move_to_operands(stack($1), stack($3));
       }
       | expr '-' expr
       {
         init($$, ID_minus);
         $2.set_location(stack($$));
         stack($$).move_to_operands(stack($1), stack($3));
       }
       | expr TOK_SLL expr
       {
         init($$, ID_shl);
         $2.set_location(stack($$));
         stack($$).move_to_operands(stack($1), stack($3));
       }
       | expr TOK_SRL expr
       {
         init($$, ID_lshr);
         $2.set_location(stack($$));
         stack($$).move_to_operands(stack($1), stack($3));
       }
       | expr TOK_SLA expr
       {
         init($$, ID_shl);
         $2.set_location(stack($$));
         stack($$).move_to_operands(stack($1), stack($3));
       }
       | expr TOK_SRA expr
       {
         init($$, ID_ashr);
         $2.set_location(stack($$));
         stack($$).move_to_operands(stack($1), stack($3));
       }
       | expr TOK_ROL expr
       {
         init($$, ID_rol);
         $2.set_location(stack($$));
         stack($$).move_to_operands(stack($1), stack($3));
       }
       | expr TOK_ROR expr
       {
         init($$, ID_ror);
         $2.set_location(stack($$));
         stack($$).move_to_operands(stack($1), stack($3));
       }
       | expr '*' expr
       {
         init($$, ID_mult);
         $2.set_location(stack($$));
         stack($$).move_to_operands(stack($1), stack($3));
       }
       | expr '/' expr
       {
         init($$, ID_div);
         $2.set_location(stack($$));
         stack($$).move_to_operands(stack($1), stack($3));
       }
       | expr TOK_MOD expr
       {
         init($$, ID_mod);
         $2.set_location(stack($$));
         stack($$).move_to_operands(stack($1), stack($3));
       }
       | TOK_NOT expr
       {
         init($$, ID_not);
         $1.set_location(stack($$));
         mto($$, $2);
       }
       | expr TOK_AND expr
       {
         init($$, ID_and);
         $2.set_location(stack($$));
         stack($$).move_to_operands(stack($1), stack($3));
       }
       | expr TOK_NAND expr
       {
         init($$, ID_nand);
         $2.set_location(stack($$));
         stack($$).move_to_operands(stack($1), stack($3));
       }
       | expr TOK_OR expr
       {
         init($$, ID_or);
         $2.set_location(stack($$));
         stack($$).move_to_operands(stack($1), stack($3));
       }
       | expr TOK_NOR expr
       {
         init($$, ID_nor);
         $2.set_location(stack($$));
         stack($$).move_to_operands(stack($1), stack($3));
       }
       | expr TOK_XOR expr
       {
         init($$, ID_xor);
         $2.set_location(stack($$));
         stack($$).move_to_operands(stack($1), stack($3));
       }
       | expr TOK_XNOR expr
       {
         init($$, ID_xnor);
         $2.set_location(stack($$));
         stack($$).move_to_operands(stack($1), stack($3));
       }
       | name '(' expr_list ')'
       {
         init($$, ID_side_effect);
         $2.set_location(stack($$));
         stack($$).set(ID_statement, ID_function_call);
         stack($$).add(ID_operands).get_sub().swap(stack($3).get_sub());
       }
       | '(' expr ')'
       {
         $$=$2;
       }
       | expr '=' expr
       {
         init($$, ID_equal);
         $2.set_location(stack($$));
         stack($$).move_to_operands(stack($1), stack($3));
       }
       | expr '>' expr
       {
         init($$, ID_gt);
         $2.set_location(stack($$));
         stack($$).move_to_operands(stack($1), stack($3));
       }
       | expr TOK_GE expr
       {
         init($$, ID_ge);
         $2.set_location(stack($$));
         stack($$).move_to_operands(stack($1), stack($3));
       }
       | expr '<' expr
       {
         init($$, ID_lt);
         $2.set_location(stack($$));
         stack($$).move_to_operands(stack($1), stack($3));
       }
       | expr TOK_LE expr
       {
         init($$, ID_le);
         $2.set_location(stack($$));
         stack($$).move_to_operands(stack($1), stack($3));
       }
       | expr TOK_NE expr
       {
         init($$, ID_notequal);
         $2.set_location(stack($$));
         stack($$).move_to_operands(stack($1), stack($3));
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
