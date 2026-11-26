%{

// Based on the syntax summary in Annex C of IEEE 1076-2008,
// restricted to the constructs needed for RTL synthesis
// (IEEE 1076.6-2004).

#include <cstring>
#include <iostream>

#include <util/dstring.h>
#include <util/std_expr.h>

#include "vhdl_expr.h"
#include "vhdl_parser.h"
#include "vhdl_types.h"

#define PARSER (*vhdl_parser_ptr)
#define YYSTYPE vhdl_parsert::yystypet

#undef stack
#undef stack_type
#define stack(x) (PARSER.stack[x.stack_index])
#define stack_type(x) (static_cast<typet &>(static_cast<irept &>(PARSER.stack[x.stack_index])))

#define mto(x, y) stack(x).add_to_operands(std::move(stack(y)))
#define mto2(dest, s1, s2) stack(dest).add_to_operands(std::move(stack(s1)), std::move(stack(s2)))
#define mto3(dest, s1, s2, s3) stack(dest).add_to_operands(std::move(stack(s1)), std::move(stack(s2)), std::move(stack(s3)))
#define mts(x, y) stack(x).move_to_sub(stack(y))

/*******************************************************************\

Function: yyvhdllex

  Inputs:

 Outputs:

 Purpose: Get the next token from the scanner. The previous token is
          remembered, to tell apart a character literal from the tick
          of an attribute name or a qualified expression, e.g. in
          std_logic'('1').

\*******************************************************************/

int yyvhdllex()
{
  int token = PARSER.scanner->lex();
  PARSER.last_token = token;
  return token;
}

/*******************************************************************\

Function: yyvhdlerror

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

extern YYSTYPE yyvhdllval;

int yyvhdlerror(const char *error_str)
{
  PARSER.syntax_error(error_str, PARSER.scanner->text());
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

/*******************************************************************\

Function: binary

  Inputs:

 Outputs:

 Purpose: Build a binary expression; the location is that of the operator.

\*******************************************************************/

inline static void binary(
  YYSTYPE &dest, YYSTYPE &op0, YYSTYPE &op, YYSTYPE &op1, const irep_idt &id)
{
  init(dest, id);
  op.set_location(stack(dest));
  mto2(dest, op0, op1);
}

/*******************************************************************\

Function: unary

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

inline static void unary(
  YYSTYPE &dest, YYSTYPE &op, YYSTYPE &op0, const irep_idt &id)
{
  init(dest, id);
  op.set_location(stack(dest));
  mto(dest, op0);
}

/*******************************************************************\

Function: set_label

  Inputs:

 Outputs:

 Purpose: Attach the identifier given as label to the statement.

\*******************************************************************/

inline static void set_label(YYSTYPE &statement, YYSTYPE &label)
{
  to_vhdl_statement(stack(statement))
    .set_label(to_symbol_expr(stack(label)).get_identifier());
}

/*******************************************************************\

Function: make_subtype_indication

  Inputs:

 Outputs:

 Purpose: Turn a name into a subtype indication. The name may carry
          an index constraint, in the form of an indexed name or a
          slice, e.g., std_logic_vector(7 downto 0).

\*******************************************************************/

inline static void make_subtype_indication(YYSTYPE &dest, YYSTYPE &name)
{
  init(dest);
  exprt &name_expr = stack(name);
  auto source_location = name_expr.source_location();

  if(name_expr.id() == ID_vhdl_slice)
  {
    // one range
    auto &slice = to_vhdl_slice_expr(name_expr);
    vhdl_subtype_indicationt result{slice.prefix()};
    result.index_constraint().push_back(slice.range());
    stack_type(dest) = std::move(result);
  }
  else if(name_expr.id() == ID_vhdl_indexed)
  {
    // the arguments are discrete ranges or subtype names
    auto &indexed = to_vhdl_indexed_expr(name_expr);
    vhdl_subtype_indicationt result{indexed.prefix()};
    for(std::size_t i = 0; i < indexed.number_of_arguments(); i++)
      result.index_constraint().push_back(indexed.argument(i).actual());
    stack_type(dest) = std::move(result);
  }
  else
    stack_type(dest) = vhdl_subtype_indicationt{std::move(name_expr)};

  stack(dest).add_source_location() = source_location;
}

%}

%{
// IEEE 1076-2008 9.2.1
%}

%left TOK_OR TOK_NOR TOK_XOR TOK_XNOR TOK_AND TOK_NAND
%nonassoc '=' TOK_NE '<' '>' TOK_GE TOK_LE
%left TOK_SLL TOK_SRL TOK_SLA TOK_SRA TOK_ROL TOK_ROR
%left '+' '-' '&'
%right UMINUS UPLUS
%left TOK_MOD TOK_REM '*' '/'
%right TOK_DOUBLE_STAR TOK_ABS TOK_NOT TOK_CONDITION

%token TOK_ARROW "=>"
%token TOK_DOUBLE_STAR "**"
%token TOK_ASSIGN ":="
%token TOK_NE "/="
%token TOK_GE ">="
%token TOK_LE "<="
%token TOK_LEFT_LABEL_BRACKET "<<"
%token TOK_RIGHT_LABEL_BRACKET ">>"
%token TOK_BOX "<>"
%token TOK_CONDITION "??"

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
%token TOK_CONTEXT "CONTEXT"
%token TOK_DISCONNECT "DISCONNECT" 
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
%token TOK_SHARED "SHARED"
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
%token TOK_REAL
%token TOK_BASED_INTEGER
%token TOK_STRING
%token TOK_BIT_STRING
%token TOK_CHAR
%token TOK_IDENTIFIER

%%

/* IEEE 1076-2008 13.1 */

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

/* IEEE 1076-2008 12.4 */
use_clause:
         TOK_USE name_list ';'
       {
         vhdl_parse_treet::itemt &u=PARSER.new_use_item();
         $1.set_location(u);
         u.get_sub().swap(stack($2).get_sub());
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

/* IEEE 1076-2008 13.2 */
library_clause:
         TOK_LIBRARY identifier_list ';'
       {
         vhdl_parse_treet::itemt &l=PARSER.new_library_item();
         $1.set_location(l);
         l.get_sub().swap(stack($2).get_sub());
       }
       ;

library_unit:
         primary_unit
       | secondary_unit
       ;

primary_unit:
         entity_declaration
       | package_declaration
       ;

secondary_unit:
         architecture_body
       | package_body
       ;

/* IEEE 1076-2008 4.7 */
package_declaration:
         TOK_PACKAGE identifier TOK_IS declarative_part
         TOK_END package_opt name_opt ';'
       {
         vhdl_parse_treet::itemt &p=PARSER.new_package_item();
         $1.set_location(p);
         p.set_name(stack($2));
         p.add(ID_decl).get_sub().swap(stack($4).get_sub());
       }
       ;

package_opt:
         /* Empty */
       | TOK_PACKAGE
       ;

/* IEEE 1076-2008 4.8 */
package_body:
         TOK_PACKAGE TOK_BODY identifier TOK_IS declarative_part
         TOK_END package_body_opt name_opt ';'
       {
         vhdl_parse_treet::itemt &p=PARSER.new_package_body_item();
         $1.set_location(p);
         p.set_name(stack($3));
         p.add(ID_decl).get_sub().swap(stack($5).get_sub());
       }
       ;

package_body_opt:
         /* Empty */
       | TOK_PACKAGE TOK_BODY
       ;

/* IEEE 1076-2008 3.2 */
entity_declaration:
         TOK_ENTITY identifier TOK_IS
         generic_clause_opt
         port_clause_opt
         declarative_part
         entity_statement_part_opt
         TOK_END entity_opt name_opt ';'
       {
         vhdl_parse_treet::itemt &e=PARSER.new_entity_item();
         $1.set_location(e);
         e.set_name(stack($2));
         e.add(ID_vhdl_generics).get_sub().swap(stack($4).get_sub());
         e.add(ID_ports).get_sub().swap(stack($5).get_sub());
         e.add(ID_decl).get_sub().swap(stack($6).get_sub());
         e.add(ID_body).get_sub().swap(stack($7).get_sub());
       }
       ;

entity_opt:
         /* Empty */
       | TOK_ENTITY
       ;

entity_statement_part_opt:
         /* Empty */
       {
         init($$);
       }
       | TOK_BEGIN concurrent_statement_list
       {
         $$=$2;
       }
       ;

/* IEEE 1076-2008 6.5.6.2 */
generic_clause_opt:
         /* Empty */
       {
         init($$);
       }
       | TOK_GENERIC '(' interface_list ')' ';'
       {
         $$=$3;
       }
       ;

/* IEEE 1076-2008 6.5.6.3 */
port_clause_opt:
         /* Empty */
       {
         init($$);
       }
       | TOK_PORT '(' interface_list ')' ';'
       {
         $$=$3;
       }
       ;

/* IEEE 1076-2008 6.5.6.1 */
interface_list:
         interface_element
       {
         init($$);
         mts($$, $1);
       }
       | interface_list ';' interface_element
       {
         $$=$1;
         mts($$, $3);
       }
       ;

/* IEEE 1076-2008 6.5.2 */
interface_element:
         interface_class_opt identifier_list ':' mode_opt subtype_indication
         bus_opt init_opt
       {
         init($$, ID_port);
         stack($$).set(ID_class, stack($1).id());
         stack($$).add(ID_vhdl_declarators).get_sub().swap(stack($2).get_sub());
         stack($$).set(ID_mode, stack($4).id());
         stack($$).add(ID_type) = stack($5);
         stack($$).add(ID_init) = stack($7);
       }
       ;

interface_class_opt:
         /* Empty */
       {
         init($$, ID_nil);
       }
       | TOK_CONSTANT
       {
         init($$, ID_constant);
       }
       | TOK_SIGNAL
       {
         init($$, ID_signal);
       }
       | TOK_VARIABLE
       {
         init($$, ID_vhdl_variable);
       }
       ;

mode_opt:
         /* Empty */
       {
         init($$, ID_input);
       }
       | TOK_IN
       {
         init($$, ID_input);
       }
       | TOK_OUT
       {
         init($$, ID_output);
       }
       | TOK_INOUT
       {
         init($$, ID_inout);
       }
       | TOK_BUFFER
       {
         init($$, ID_vhdl_buffer);
       }
       | TOK_LINKAGE
       {
         init($$, ID_linkage);
       }
       ;

bus_opt:
         /* Empty */
       | TOK_BUS
       ;

init_opt:
         /* Empty */
       {
         init($$, ID_nil);
       }
       | TOK_ASSIGN expr
       {
         $$=$2;
       }
       ;

/* IEEE 1076-2008 3.3 */
architecture_body:
         TOK_ARCHITECTURE identifier TOK_OF name TOK_IS
         declarative_part
         TOK_BEGIN concurrent_statement_list
         TOK_END architecture_opt name_opt ';'
       {
         vhdl_parse_treet::itemt &a=PARSER.new_architecture_item();
         $1.set_location(a);
         a.set_name(stack($2));
         a.add(ID_entity) = stack($4);
         a.add(ID_decl).get_sub().swap(stack($6).get_sub());
         a.add(ID_body).get_sub().swap(stack($8).get_sub());
       }
       ;

architecture_opt:
         /* Empty */
       | TOK_ARCHITECTURE
       ;

/* Declarations; IEEE 1076-2008 3.2.3, 3.3.2, 4.3, 4.7, 11.3.
   We use one list for all declarative regions. */

declarative_part:
         /* Empty */
       {
         init($$);
       }
       | declarative_part declarative_item
       {
         $$=$1;
         if(stack($2).is_not_nil())
           mts($$, $2);
       }
       ;

declarative_item:
         signal_declaration
       | constant_declaration
       | variable_declaration
       | type_declaration
       | subtype_declaration
       | component_declaration
       | subprogram_declaration
       | subprogram_body
       | alias_declaration
       | attribute_declaration
       | attribute_specification
       | configuration_specification
       | use_clause
       {
         init($$, ID_nil);
       }
       ;

/* IEEE 1076-2008 7.3; ignored */
configuration_specification:
         TOK_FOR instantiation_list ':' name TOK_USE binding_indication ';'
       {
         init($$, ID_nil);
       }
       ;

instantiation_list:
         identifier_list
       | TOK_OTHERS
       | TOK_ALL
       ;

binding_indication:
         TOK_ENTITY name generic_map_aspect_opt port_map_aspect_opt
       | TOK_CONFIGURATION name generic_map_aspect_opt port_map_aspect_opt
       | TOK_OPEN generic_map_aspect_opt port_map_aspect_opt
       ;

/* IEEE 1076-2008 6.4.2.3 */
signal_declaration:
         TOK_SIGNAL identifier_list ':' subtype_indication signal_kind_opt init_opt ';'
       {
         init($$, ID_signal);
         $1.set_location(stack($$));
         stack($$).add(ID_vhdl_declarators).get_sub().swap(stack($2).get_sub());
         stack($$).add(ID_type) = stack($4);
         stack($$).add(ID_init) = stack($6);
       }
       ;

signal_kind_opt:
         /* Empty */
       | TOK_REGISTER
       | TOK_BUS
       ;

/* IEEE 1076-2008 6.4.2.2 */
constant_declaration:
         TOK_CONSTANT identifier_list ':' subtype_indication init_opt ';'
       {
         init($$, ID_constant);
         $1.set_location(stack($$));
         stack($$).add(ID_vhdl_declarators).get_sub().swap(stack($2).get_sub());
         stack($$).add(ID_type) = stack($4);
         stack($$).add(ID_init) = stack($5);
       }
       ;

/* IEEE 1076-2008 6.4.2.4 */
variable_declaration:
         shared_opt TOK_VARIABLE identifier_list ':' subtype_indication init_opt ';'
       {
         init($$, ID_vhdl_variable);
         $2.set_location(stack($$));
         stack($$).add(ID_vhdl_declarators).get_sub().swap(stack($3).get_sub());
         stack($$).add(ID_type) = stack($5);
         stack($$).add(ID_init) = stack($6);
       }
       ;

shared_opt:
         /* Empty */
       | TOK_SHARED
       ;

/* IEEE 1076-2008 6.2 */
type_declaration:
         TOK_TYPE identifier TOK_IS type_definition ';'
       {
         init($$, ID_vhdl_type_decl);
         $1.set_location(stack($$));
         stack($$).add(ID_name) = stack($2);
         stack($$).add(ID_type) = stack($4);
       }
       | TOK_TYPE identifier ';'
       {
         // incomplete type declaration
         init($$, ID_vhdl_type_decl);
         $1.set_location(stack($$));
         stack($$).add(ID_name) = stack($2);
         stack($$).add(ID_type).id(ID_nil);
       }
       ;

type_definition:
         enumeration_type_definition
       | range_type_definition
       | array_type_definition
       | record_type_definition
       ;

/* IEEE 1076-2008 5.2.2 */
enumeration_type_definition:
         '(' enumeration_literal_list ')'
       {
         init($$);
         vhdl_enumeration_type_definitiont result;
         result.elements().swap(stack($2).get_sub());
         stack_type($$) = std::move(result);
         $1.set_location(stack($$));
       }
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
         identifier
       | character_literal
       ;

/* IEEE 1076-2008 5.2.3, 5.2.4; the physical units are ignored */
range_type_definition:
         TOK_RANGE range physical_units_opt
       {
         init($$);
         stack_type($$) = vhdl_integer_type_definitiont{std::move(stack($2))};
         $1.set_location(stack($$));
       }
       ;

physical_units_opt:
         /* Empty */
       | TOK_UNITS identifier ';' secondary_units TOK_END TOK_UNITS name_opt
       ;

secondary_units:
         /* Empty */
       | secondary_units identifier '=' physical_literal ';'
       ;

physical_literal:
         TOK_NATURAL identifier
       | identifier
       ;

/* IEEE 1076-2008 5.3.2 */
array_type_definition:
         TOK_ARRAY '(' index_subtype_definition_list ')' TOK_OF subtype_indication
       {
         init($$);
         vhdl_array_type_definitiont result{std::move(stack_type($6))};
         result.index_constraint().swap(stack($3).get_sub());
         stack_type($$) = std::move(result);
         $1.set_location(stack($$));
       }
       ;

index_subtype_definition_list:
         index_subtype_definition
       {
         init($$);
         mts($$, $1);
       }
       | index_subtype_definition_list ',' index_subtype_definition
       {
         $$=$1;
         mts($$, $3);
       }
       ;

index_subtype_definition:
         name TOK_RANGE TOK_BOX
       {
         init($$, ID_vhdl_unconstrained);
         $2.set_location(stack($$));
         stack($$).add(ID_type) = stack($1);
       }
       | discrete_range
       ;

/* IEEE 1076-2008 5.3.2.1 */
discrete_range:
         range
       | name TOK_RANGE range
       {
         // a subtype indication with a range constraint
         init($$);
         vhdl_subtype_indicationt result{std::move(stack($1))};
         result.range_constraint(std::move(stack($3)));
         stack_type($$) = std::move(result);
         $2.set_location(stack($$));
       }
       ;

/* IEEE 1076-2008 5.2.1 */
range:
         expr updown expr
       {
         init($$);
         stack($$) = vhdl_range_exprt{
           std::move(stack($1)), stack($2).id(), std::move(stack($3))};
         $2.set_location(stack($$));
       }
       | expr
       {
         // this must be a range attribute, e.g., v'range
         $$=$1;
       }
       ;

updown: 
         TOK_DOWNTO
       {
         init($$, ID_vhdl_downto);
       }
       | TOK_TO
       {
         init($$, ID_to);
       }
       ;

/* IEEE 1076-2008 5.3.3 */
record_type_definition:
         TOK_RECORD element_declaration_list TOK_END TOK_RECORD name_opt
       {
         init($$);
         vhdl_record_type_definitiont result;
         result.elements().swap(stack($2).get_sub());
         stack_type($$) = std::move(result);
         $1.set_location(stack($$));
       }
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
         identifier_list ':' subtype_indication ';'
       {
         init($$, ID_component);
         stack($$).add(ID_vhdl_declarators).get_sub().swap(stack($1).get_sub());
         stack($$).add(ID_type) = stack($3);
       }
       ;

/* IEEE 1076-2008 6.3 */
subtype_declaration:
         TOK_SUBTYPE identifier TOK_IS subtype_indication ';'
       {
         init($$, ID_vhdl_subtype_decl);
         $1.set_location(stack($$));
         stack($$).add(ID_name) = stack($2);
         stack($$).add(ID_type) = stack($4);
       }
       ;

/* IEEE 1076-2008 6.3; the resolution function indication is not supported.
   An index constraint is parsed as an indexed name or a slice, and
   split off here. */
subtype_indication:
         name
       {
         make_subtype_indication($$, $1);
       }
       | name TOK_RANGE range
       {
         init($$);
         vhdl_subtype_indicationt result{std::move(stack($1))};
         result.range_constraint(std::move(stack($3)));
         stack_type($$) = std::move(result);
         $2.set_location(stack($$));
       }
       ;

/* IEEE 1076-2008 6.8 */
component_declaration:
         TOK_COMPONENT identifier is_opt
         generic_clause_opt
         port_clause_opt
         TOK_END TOK_COMPONENT name_opt ';'
       {
         init($$, ID_component);
         $1.set_location(stack($$));
         stack($$).add(ID_name) = stack($2);
         stack($$).add(ID_vhdl_generics).get_sub().swap(stack($4).get_sub());
         stack($$).add(ID_ports).get_sub().swap(stack($5).get_sub());
       }
       ;

is_opt:
         /* Empty */
       | TOK_IS
       ;

/* IEEE 1076-2008 4.2 */
subprogram_declaration:
         subprogram_specification ';'
       {
         $$=$1;
       }
       ;

subprogram_specification:
         purity_opt TOK_FUNCTION designator parameter_list_opt TOK_RETURN name
       {
         init($$, ID_vhdl_function);
         $2.set_location(stack($$));
         stack($$).set(ID_vhdl_pure, stack($1).id() != ID_vhdl_impure);
         stack($$).add(ID_name) = stack($3);
         stack($$).add(ID_parameters).get_sub().swap(stack($4).get_sub());
         stack($$).add(ID_return_type) = stack($6);
       }
       | TOK_PROCEDURE designator parameter_list_opt
       {
         init($$, ID_vhdl_procedure);
         $1.set_location(stack($$));
         stack($$).add(ID_name) = stack($2);
         stack($$).add(ID_parameters).get_sub().swap(stack($3).get_sub());
       }
       ;

purity_opt:
         /* Empty */
       {
         init($$, ID_nil);
       }
       | TOK_PURE
       {
         init($$, ID_vhdl_pure);
       }
       | TOK_IMPURE
       {
         init($$, ID_vhdl_impure);
       }
       ;

designator:
         identifier
       | TOK_STRING
       {
         // operator symbol
         init($$, ID_symbol);
         $1.set_location(stack($$));
         stack($$).set(ID_identifier, $1.text);
       }
       ;

parameter_list_opt:
         /* Empty */
       {
         init($$);
       }
       | '(' interface_list ')'
       {
         $$=$2;
       }
       ;

/* IEEE 1076-2008 4.3 */
subprogram_body:
         subprogram_specification TOK_IS
         declarative_part
         TOK_BEGIN sequence_of_statements
         TOK_END subprogram_kind_opt designator_opt ';'
       {
         $$=$1;
         stack($$).add(ID_decl).get_sub().swap(stack($3).get_sub());
         stack($$).add(ID_body) = stack($5);
       }
       ;

designator_opt:
         /* Empty */
       | designator
       ;

subprogram_kind_opt:
         /* Empty */
       | TOK_FUNCTION
       | TOK_PROCEDURE
       ;

/* IEEE 1076-2008 6.6 */
alias_declaration:
         TOK_ALIAS identifier ':' subtype_indication TOK_IS name ';'
       {
         init($$, ID_alias);
         $1.set_location(stack($$));
         stack($$).add(ID_name) = stack($2);
         stack($$).add(ID_type) = stack($4);
         stack($$).add(ID_value) = stack($6);
       }
       | TOK_ALIAS identifier TOK_IS name ';'
       {
         init($$, ID_alias);
         $1.set_location(stack($$));
         stack($$).add(ID_name) = stack($2);
         stack($$).add(ID_type).id(ID_nil);
         stack($$).add(ID_value) = stack($4);
       }
       ;

/* IEEE 1076-2008 6.7; ignored */
attribute_declaration:
         TOK_ATTRIBUTE identifier ':' name ';'
       {
         init($$, ID_nil);
       }
       ;

/* IEEE 1076-2008 7.2; ignored */
attribute_specification:
         TOK_ATTRIBUTE identifier TOK_OF entity_name_list ':' entity_class TOK_IS expr ';'
       {
         init($$, ID_nil);
       }
       ;

entity_name_list:
         identifier_list
       | TOK_OTHERS
       | TOK_ALL
       ;

entity_class:
         TOK_ENTITY | TOK_ARCHITECTURE | TOK_CONFIGURATION | TOK_PROCEDURE
       | TOK_FUNCTION | TOK_PACKAGE | TOK_TYPE | TOK_SUBTYPE | TOK_CONSTANT
       | TOK_SIGNAL | TOK_VARIABLE | TOK_COMPONENT | TOK_LABEL | TOK_LITERAL
       | TOK_UNITS | TOK_GROUP | TOK_FILE
       ;

/* Concurrent statements; IEEE 1076-2008 Clause 11 */

concurrent_statement_list:
         /* Empty */
       {
         init($$);
       }
       | concurrent_statement_list concurrent_statement
       {
         $$=$1;
         mts($$, $2);
       }
       ;

concurrent_statement:
         identifier ':' concurrent_statement_body
       {
         $$=$3;
         set_label($$, $1);
       }
       | concurrent_statement_body
       {
         // IEEE 1076-2008 11.7, 11.8: instantiations and generate
         // statements must be labelled
         if(stack($$).id() == ID_inst ||
            stack($$).id() == ID_generate_for ||
            stack($$).id() == ID_generate_if)
         {
           PARSER.syntax_error("label required", "");
           YYERROR;
         }
       }
       ;

concurrent_statement_body:
         process_statement
       | TOK_POSTPONED process_statement
       {
         $$=$2;
       }
       | concurrent_assertion_statement
       | concurrent_signal_assignment_statement
       | component_instantiation_statement
       | generate_statement
       ;

/* IEEE 1076-2008 11.3 */
process_statement:
         TOK_PROCESS sensitivity_opt is_opt
         declarative_part
         TOK_BEGIN sequence_of_statements
         TOK_END postponed_opt TOK_PROCESS name_opt ';'
       {
         init($$);
         irept declarations;
         declarations.get_sub().swap(stack($4).get_sub());
         stack($$) = vhdl_processt{
           std::move(stack($2)), std::move(declarations), std::move(stack($6))};
         $1.set_location(stack($$));
       }
       ;

postponed_opt:
         /* Empty */
       | TOK_POSTPONED
       ;

sensitivity_opt:
         /* Empty */
       {
         init($$, ID_nil);
       }
       | '(' name_list ')'
       {
         $$=$2;
       }
       | '(' TOK_ALL ')'
       {
         init($$, ID_all);
       }
       ;

/* IEEE 1076-2008 11.5 */
concurrent_assertion_statement:
         assertion ';'
       {
         $$=$1;
       }
       | TOK_POSTPONED assertion ';'
       {
         $$=$2;
       }
       ;

/* IEEE 1076-2008 10.3 */
assertion:
         TOK_ASSERT expr report_opt severity_opt
       {
         init($$, ID_assert);
         $1.set_location(stack($$));
         mto($$, $2);
         stack($$).add(ID_vhdl_report) = stack($3);
         stack($$).add(ID_vhdl_severity) = stack($4);
       }
       ;

report_opt:
         /* Empty */
       {
         init($$, ID_nil);
       }
       | TOK_REPORT expr
       {
         $$=$2;
       }
       ;

severity_opt:
         /* Empty */
       {
         init($$, ID_nil);
       }
       | TOK_SEVERITY expr
       {
         $$=$2;
       }
       ;

/* IEEE 1076-2008 11.6 */
concurrent_signal_assignment_statement:
         name TOK_LE guarded_opt delay_mechanism_opt conditional_waveforms ';'
       {
         init($$);
         stack($$) = vhdl_signal_assignt{std::move(stack($1)), std::move(stack($5))};
         $2.set_location(stack($$));
       }
       | TOK_WITH expr TOK_SELECT name TOK_LE
         guarded_opt delay_mechanism_opt selected_waveforms ';'
       {
         init($$);
         vhdl_selected_assignt result{std::move(stack($4)), std::move(stack($2)), false};
         result.alternatives().swap(stack($8).get_sub());
         stack($$) = std::move(result);
         $1.set_location(stack($$));
       }
       ;

guarded_opt:
         /* Empty */
       | TOK_GUARDED
       ;

/* IEEE 1076-2008 10.5.2.1; the delay is ignored */
delay_mechanism_opt:
         /* Empty */
       | TOK_TRANSPORT
       | TOK_INERTIAL
       | TOK_REJECT expr TOK_INERTIAL
       ;

/* IEEE 1076-2008 10.5.3; the result is nested if-expressions,
   with a nil else branch when there is none */
conditional_waveforms:
         waveform
       | waveform TOK_WHEN expr
       {
         init($$, ID_if);
         $2.set_location(stack($$));
         mto2($$, $3, $1);
         stack($$).operands().emplace_back(nil_exprt{});
       }
       | waveform TOK_WHEN expr TOK_ELSE conditional_waveforms
       {
         init($$, ID_if);
         $2.set_location(stack($$));
         mto3($$, $3, $1, $5);
       }
       ;

/* IEEE 1076-2008 10.5.4 */
selected_waveforms:
         selected_waveform
       {
         init($$);
         mts($$, $1);
       }
       | selected_waveforms ',' selected_waveform
       {
         $$=$1;
         mts($$, $3);
       }
       ;

selected_waveform:
         waveform TOK_WHEN choices
       {
         init($$, ID_case_item);
         $2.set_location(stack($$));
         stack($$).add(ID_vhdl_choices).get_sub().swap(stack($3).get_sub());
         mto($$, $1);
       }
       ;

/* IEEE 1076-2008 10.5.2.1; only one waveform element is supported,
   and the delay is ignored */
waveform:
         expr
       | expr TOK_AFTER expr
       {
         $$=$1;
       }
       | TOK_UNAFFECTED
       {
         init($$, ID_nil);
       }
       ;

/* IEEE 1076-2008 11.7 */
/* A name followed by a semicolon is a concurrent procedure call
   (IEEE 1076-2008 11.4); it is an instantiation when there is a
   generic map or port map. */
component_instantiation_statement:
         instantiated_unit generic_map_aspect_opt port_map_aspect_opt ';'
       {
         $$=$1;
         if(stack($2).get_sub().empty() && stack($3).get_sub().empty() &&
            stack($$).find(ID_entity).is_nil())
         {
           exprt call(ID_function_call);
           call.add_source_location() = stack($$).source_location();
           call.add_to_operands(std::move(static_cast<exprt &>(stack($$).add(ID_component))));
           stack($$) = std::move(call);
         }
         else
         {
           stack($$).add(ID_vhdl_generic_map).get_sub().swap(stack($2).get_sub());
           stack($$).add(ID_vhdl_port_map).get_sub().swap(stack($3).get_sub());
         }
       }
       ;

/* The form "component name" is not supported, as it conflicts
   with component declarations in generate statement bodies.
   The architecture of a direct entity instantiation, entity(arch),
   is parsed as an indexed name. */
instantiated_unit:
         name
       {
         init($$, ID_inst);
         stack($$).add_source_location() = stack($1).source_location();
         stack($$).add(ID_component) = stack($1);
       }
       | TOK_ENTITY name
       {
         init($$, ID_inst);
         $1.set_location(stack($$));
         stack($$).add(ID_entity) = stack($2);
       }
       ;

generic_map_aspect_opt:
         /* Empty */
       {
         init($$);
       }
       | TOK_GENERIC TOK_MAP '(' association_list ')'
       {
         $$=$4;
       }
       ;

port_map_aspect_opt:
         /* Empty */
       {
         init($$);
       }
       | TOK_PORT TOK_MAP '(' association_list ')'
       {
         $$=$4;
       }
       ;

/* IEEE 1076-2008 6.5.7.1 */
association_list:
         association_element
       {
         init($$);
         mts($$, $1);
       }
       | association_list ',' association_element
       {
         $$=$1;
         mts($$, $3);
       }
       ;

association_element:
         actual
       {
         init($$);
         stack($$) = vhdl_associationt{nil_exprt{}, std::move(stack($1))};
       }
       | name TOK_ARROW actual
       {
         init($$);
         stack($$) = vhdl_associationt{std::move(stack($1)), std::move(stack($3))};
         $2.set_location(stack($$));
       }
       ;

actual:
         expr
       | TOK_OPEN
       {
         init($$, ID_vhdl_open);
         $1.set_location(stack($$));
       }
       ;

/* IEEE 1076-2008 11.8 */
generate_statement:
         TOK_FOR identifier TOK_IN discrete_range TOK_GENERATE
         generate_statement_body
         TOK_END TOK_GENERATE name_opt ';'
       {
         init($$, ID_generate_for);
         $1.set_location(stack($$));
         stack($$).add(ID_vhdl_loop_variable) = stack($2);
         stack($$).add(ID_range) = stack($4);
         stack($$).add(ID_body) = stack($6);
       }
       | TOK_IF expr TOK_GENERATE
         generate_statement_body
         TOK_END TOK_GENERATE name_opt ';'
       {
         init($$, ID_generate_if);
         $1.set_location(stack($$));
         mto($$, $2);
         stack($$).add(ID_body) = stack($4);
       }
       ;

/* The optional declarative part of a generate statement body is not
   supported; it conflicts with component instantiations and
   configuration specifications. */
generate_statement_body:
         concurrent_statement_list
       {
         init($$, ID_generate_block);
         stack($$).add(ID_body).get_sub().swap(stack($1).get_sub());
       }
       ;

/* Sequential statements; IEEE 1076-2008 Clause 10 */

sequence_of_statements:
         /* Empty */
       {
         init($$, ID_block);
       }
       | sequence_of_statements sequential_statement
       {
         $$=$1;
         mto($$, $2);
       }
       ;

sequential_statement:
         identifier ':' sequential_statement_body
       {
         $$=$3;
         set_label($$, $1);
       }
       | sequential_statement_body
       ;

sequential_statement_body:
         wait_statement
       | assertion_statement
       | report_statement
       | signal_assignment_statement
       | variable_assignment_statement
       | procedure_call_statement
       | if_statement
       | case_statement
       | loop_statement
       | next_statement
       | exit_statement
       | return_statement
       | null_statement
       ;

/* IEEE 1076-2008 10.2 */
wait_statement:
         TOK_WAIT sensitivity_clause_opt condition_clause_opt timeout_clause_opt ';'
       {
         init($$, ID_wait);
         $1.set_location(stack($$));
         stack($$).add(ID_vhdl_sensitivity) = stack($2);
         mto($$, $3);
       }
       ;

sensitivity_clause_opt:
         /* Empty */
       {
         init($$, ID_nil);
       }
       | TOK_ON name_list
       {
         $$=$2;
       }
       ;

condition_clause_opt:
         /* Empty */
       {
         init($$, ID_nil);
       }
       | TOK_UNTIL expr
       {
         $$=$2;
       }
       ;

timeout_clause_opt:
         /* Empty */
       | TOK_FOR expr
       ;

/* IEEE 1076-2008 10.3 */
assertion_statement:
         assertion ';'
       {
         $$=$1;
       }
       ;

/* IEEE 1076-2008 10.4 */
report_statement:
         TOK_REPORT expr severity_opt ';'
       {
         init($$, ID_vhdl_report);
         $1.set_location(stack($$));
         mto($$, $2);
         stack($$).add(ID_vhdl_severity) = stack($3);
       }
       ;

/* IEEE 1076-2008 10.5; conditional and selected forms are VHDL-2008 */
signal_assignment_statement:
         name TOK_LE delay_mechanism_opt conditional_waveforms ';'
       {
         init($$);
         stack($$) = vhdl_signal_assignt{std::move(stack($1)), std::move(stack($4))};
         $2.set_location(stack($$));
       }
       | TOK_WITH expr TOK_SELECT name TOK_LE delay_mechanism_opt selected_waveforms ';'
       {
         init($$);
         vhdl_selected_assignt result{std::move(stack($4)), std::move(stack($2)), false};
         result.alternatives().swap(stack($7).get_sub());
         stack($$) = std::move(result);
         $1.set_location(stack($$));
       }
       ;

/* IEEE 1076-2008 10.6; conditional and selected forms are VHDL-2008 */
variable_assignment_statement:
         name TOK_ASSIGN conditional_expression ';'
       {
         init($$, ID_assign);
         $2.set_location(stack($$));
         mto2($$, $1, $3);
       }
       | TOK_WITH expr TOK_SELECT name TOK_ASSIGN selected_expressions ';'
       {
         init($$);
         vhdl_selected_assignt result{std::move(stack($4)), std::move(stack($2)), true};
         result.alternatives().swap(stack($6).get_sub());
         stack($$) = std::move(result);
         $1.set_location(stack($$));
       }
       ;

conditional_expression:
         expr
       | expr TOK_WHEN expr
       {
         init($$, ID_if);
         $2.set_location(stack($$));
         mto2($$, $3, $1);
         stack($$).operands().emplace_back(nil_exprt{});
       }
       | expr TOK_WHEN expr TOK_ELSE conditional_expression
       {
         init($$, ID_if);
         $2.set_location(stack($$));
         mto3($$, $3, $1, $5);
       }
       ;

selected_expressions:
         selected_expression
       {
         init($$);
         mts($$, $1);
       }
       | selected_expressions ',' selected_expression
       {
         $$=$1;
         mts($$, $3);
       }
       ;

selected_expression:
         expr TOK_WHEN choices
       {
         init($$, ID_case_item);
         $2.set_location(stack($$));
         stack($$).add(ID_vhdl_choices).get_sub().swap(stack($3).get_sub());
         mto($$, $1);
       }
       ;

/* IEEE 1076-2008 10.7 */
procedure_call_statement:
         name ';'
       {
         init($$, ID_function_call);
         stack($$).add_source_location() = stack($1).source_location();
         mto($$, $1);
       }
       ;

/* IEEE 1076-2008 10.8 */
if_statement:
         TOK_IF expr TOK_THEN sequence_of_statements
         elsif_list else_opt
         TOK_END TOK_IF name_opt ';'
       {
         // The elsif chain is turned into nested if statements,
         // starting from the innermost else branch.
         exprt else_part = std::move(stack($6));

         for(auto it = stack($5).get_sub().rbegin();
             it != stack($5).get_sub().rend();
             ++it)
         {
           exprt &elsif = static_cast<exprt &>(*it);
           elsif.add_to_operands(std::move(else_part));
           else_part = std::move(elsif);
         }

         init($$, ID_ifthenelse);
         $1.set_location(stack($$));
         mto2($$, $2, $4);
         stack($$).add_to_operands(std::move(else_part));
       }
       ;

elsif_list:
         /* Empty */
       {
         init($$);
       }
       | elsif_list TOK_ELSIF expr TOK_THEN sequence_of_statements
       {
         $$=$1;
         // an incomplete if statement; the else branch is added later
         exprt elsif(ID_ifthenelse);
         $2.set_location(elsif);
         elsif.add_to_operands(std::move(stack($3)), std::move(stack($5)));
         stack($$).move_to_sub(elsif);
       }
       ;

else_opt:
         /* Empty */
       {
         init($$, ID_nil);
       }
       | TOK_ELSE sequence_of_statements
       {
         $$=$2;
       }
       ;

/* IEEE 1076-2008 10.9 */
case_statement:
         TOK_CASE expr TOK_IS case_statement_alternatives TOK_END TOK_CASE name_opt ';'
       {
         init($$, ID_switch_case);
         $1.set_location(stack($$));
         mto($$, $2);
         stack($$).add(ID_case_item).get_sub().swap(stack($4).get_sub());
       }
       ;

case_statement_alternatives:
         case_statement_alternative
       {
         init($$);
         mts($$, $1);
       }
       | case_statement_alternatives case_statement_alternative
       {
         $$=$1;
         mts($$, $2);
       }
       ;

case_statement_alternative:
         TOK_WHEN choices TOK_ARROW sequence_of_statements
       {
         init($$, ID_case_item);
         $1.set_location(stack($$));
         stack($$).add(ID_vhdl_choices).get_sub().swap(stack($2).get_sub());
         mto($$, $4);
       }
       ;

/* IEEE 1076-2008 9.3.3.1 */
choices:
         choice
       {
         init($$);
         mts($$, $1);
       }
       | choices '|' choice
       {
         $$=$1;
         mts($$, $3);
       }
       ;

choice:
         expr
       | expr updown expr
       {
         init($$);
         stack($$) = vhdl_range_exprt{
           std::move(stack($1)), stack($2).id(), std::move(stack($3))};
         $2.set_location(stack($$));
       }
       | TOK_OTHERS
       {
         init($$, ID_vhdl_others);
         $1.set_location(stack($$));
       }
       ;

/* IEEE 1076-2008 10.10 */
loop_statement:
         TOK_WHILE expr TOK_LOOP sequence_of_statements TOK_END TOK_LOOP name_opt ';'
       {
         init($$, ID_while);
         $1.set_location(stack($$));
         mto2($$, $2, $4);
       }
       | TOK_FOR identifier TOK_IN discrete_range TOK_LOOP sequence_of_statements
         TOK_END TOK_LOOP name_opt ';'
       {
         init($$, ID_for);
         $1.set_location(stack($$));
         stack($$).add(ID_vhdl_loop_variable) = stack($2);
         stack($$).add(ID_range) = stack($4);
         mto($$, $6);
       }
       | TOK_LOOP sequence_of_statements TOK_END TOK_LOOP name_opt ';'
       {
         init($$, ID_while);
         $1.set_location(stack($$));
         stack($$).operands().emplace_back(true_exprt{});
         mto($$, $2);
       }
       ;

/* IEEE 1076-2008 10.11 */
next_statement:
         TOK_NEXT name_opt when_opt ';'
       {
         init($$, ID_vhdl_next);
         $1.set_location(stack($$));
         stack($$).add(ID_label) = stack($2);
         mto($$, $3);
       }
       ;

/* IEEE 1076-2008 10.12 */
exit_statement:
         TOK_EXIT name_opt when_opt ';'
       {
         init($$, ID_vhdl_exit);
         $1.set_location(stack($$));
         stack($$).add(ID_label) = stack($2);
         mto($$, $3);
       }
       ;

when_opt:
         /* Empty */
       {
         init($$, ID_nil);
       }
       | TOK_WHEN expr
       {
         $$=$2;
       }
       ;

/* IEEE 1076-2008 10.13 */
return_statement:
         TOK_RETURN ';'
       {
         init($$, ID_return);
         $1.set_location(stack($$));
       }
       | TOK_RETURN expr ';'
       {
         init($$, ID_return);
         $1.set_location(stack($$));
         mto($$, $2);
       }
       ;

/* IEEE 1076-2008 10.14 */
null_statement:
         TOK_NULL ';'
       {
         init($$, ID_skip);
         $1.set_location(stack($$));
       }
       ;

/* Names; IEEE 1076-2008 Clause 8.
   An indexed name, a slice, a function call, and a type conversion
   cannot be distinguished syntactically; they are all parsed as
   vhdl_indexed or vhdl_slice and resolved during type checking. */

identifier:
         TOK_IDENTIFIER
       {
         init($$, ID_symbol);
         $1.set_location(stack($$));
         stack($$).set(ID_identifier, $1.text);
       }
       ;

identifier_list:
         identifier
       {
         init($$);
         mts($$, $1);
       }
       | identifier_list ',' identifier
       {
         $$=$1;
         mts($$, $3);
       }
       ;

name:
         identifier
       | name '.' TOK_IDENTIFIER
       {
         init($$, ID_member);
         $2.set_location(stack($$));
         mto($$, $1);
         stack($$).set(ID_component_name, $3.text);
       }
       | name '.' TOK_ALL
       {
         init($$, ID_all);
         $2.set_location(stack($$));
         mto($$, $1);
       }
       | name '.' character_literal
       {
         // a selected name denoting a character literal
         init($$, ID_member);
         $2.set_location(stack($$));
         mto($$, $1);
         stack($$).set(ID_component_name, stack($3).get(ID_value));
       }
       | name '(' association_list ')'
       {
         init($$);
         vhdl_indexed_exprt result{std::move(stack($1))};
         for(auto &association : stack($3).get_sub())
           result.add_argument(
             std::move(static_cast<vhdl_associationt &>(association)));
         stack($$) = std::move(result);
         $2.set_location(stack($$));
       }
       | name '(' expr updown expr ')'
       {
         vhdl_range_exprt range{
           std::move(stack($3)), stack($4).id(), std::move(stack($5))};
         $4.set_location(range);

         init($$);
         stack($$) = vhdl_slice_exprt{std::move(stack($1)), std::move(range)};
         $2.set_location(stack($$));
       }
       | name '\'' TOK_IDENTIFIER
       {
         init($$);
         stack($$) = vhdl_attribute_exprt{std::move(stack($1)), $3.text};
         $2.set_location(stack($$));
       }
       | name '\'' TOK_RANGE
       {
         init($$);
         stack($$) = vhdl_attribute_exprt{std::move(stack($1)), "range"};
         $2.set_location(stack($$));
       }
       | name '\'' '(' expr ')'
       {
         // qualified expression
         init($$);
         stack($$) = vhdl_qualified_exprt{std::move(stack($1)), std::move(stack($4))};
         $2.set_location(stack($$));
       }
       | name '\'' aggregate
       {
         // qualified expression with an aggregate
         init($$);
         stack($$) = vhdl_qualified_exprt{std::move(stack($1)), std::move(stack($3))};
         $2.set_location(stack($$));
       }
       ;

name_opt:
         /* Empty */
       {
         init($$, ID_nil);
       }
       | name
       ;

/* Expressions; IEEE 1076-2008 Clause 9 */

character_literal:
         TOK_CHAR
       {
         init($$, ID_constant);
         $1.set_location(stack($$));
         stack($$).set(ID_type, ID_char);
         stack($$).set(ID_value, $1.text);
       }
       ;

literal:
         TOK_NATURAL
       {
         init($$, ID_constant);
         $1.set_location(stack($$));
         stack($$).set(ID_type, ID_natural);
         stack($$).set(ID_value, $1.text);
       }
       | TOK_NATURAL identifier
       {
         // physical literal, e.g., 10 ns
         init($$);
         stack($$) = vhdl_physical_literal_exprt{$1.text, stack($2).get(ID_identifier)};
         $1.set_location(stack($$));
       }
       | TOK_REAL
       {
         init($$, ID_constant);
         $1.set_location(stack($$));
         stack($$).set(ID_type, ID_real);
         stack($$).set(ID_value, $1.text);
       }
       | TOK_BASED_INTEGER
       {
         init($$, ID_constant);
         $1.set_location(stack($$));
         stack($$).set(ID_type, ID_natural);
         stack($$).set(ID_value, $1.text);
       }
       | character_literal
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
         stack($$).set(ID_type, ID_vhdl_bit_string);
         stack($$).set(ID_value, $1.text);
       }
       | TOK_NULL
       {
         init($$, ID_constant);
         $1.set_location(stack($$));
         stack($$).set(ID_type, ID_nullptr);
       }
       ;

/* IEEE 1076-2008 9.3.3; a parenthesised single expression is
   not an aggregate */
aggregate:
         '(' element_association ',' element_association_list ')'
       {
         vhdl_aggregate_exprt result;
         result.add_association(
           std::move(static_cast<vhdl_element_associationt &>(stack($2))));
         for(auto &association : stack($4).get_sub())
           result.add_association(
             std::move(static_cast<vhdl_element_associationt &>(association)));
         init($$);
         stack($$) = std::move(result);
         $1.set_location(stack($$));
       }
       | '(' choices TOK_ARROW expr ')'
       {
         vhdl_element_associationt association{std::move(stack($4))};
         association.choices().swap(stack($2).get_sub());
         $3.set_location(association);

         vhdl_aggregate_exprt result;
         result.add_association(std::move(association));
         init($$);
         stack($$) = std::move(result);
         $1.set_location(stack($$));
       }
       ;

element_association_list:
         element_association
       {
         init($$);
         mts($$, $1);
       }
       | element_association_list ',' element_association
       {
         $$=$1;
         mts($$, $3);
       }
       ;

element_association:
         expr
       {
         init($$);
         stack($$) = vhdl_element_associationt{std::move(stack($1))};
       }
       | choices TOK_ARROW expr
       {
         vhdl_element_associationt association{std::move(stack($3))};
         association.choices().swap(stack($1).get_sub());
         init($$);
         stack($$) = std::move(association);
         $2.set_location(stack($$));
       }
       ;

primary:
         name
       | literal
       | aggregate
       | '(' expr ')'
       {
         $$=$2;
       }
       ;

expr:
         primary
       | expr '&' expr   { binary($$, $1, $2, $3, ID_concatenation); }
       | '-' expr %prec UMINUS { unary($$, $1, $2, ID_unary_minus); }
       | '+' expr %prec UPLUS  { unary($$, $1, $2, ID_unary_plus); }
       | TOK_ABS expr    { unary($$, $1, $2, ID_abs); }
       | TOK_NOT expr    { unary($$, $1, $2, ID_not); }
       | TOK_CONDITION expr { unary($$, $1, $2, ID_typecast); }
       | expr '+' expr   { binary($$, $1, $2, $3, ID_plus); }
       | expr '-' expr   { binary($$, $1, $2, $3, ID_minus); }
       | expr '*' expr   { binary($$, $1, $2, $3, ID_mult); }
       | expr '/' expr   { binary($$, $1, $2, $3, ID_div); }
       | expr TOK_MOD expr { binary($$, $1, $2, $3, ID_mod); }
       | expr TOK_REM expr { binary($$, $1, $2, $3, ID_vhdl_rem); }
       | expr TOK_DOUBLE_STAR expr { binary($$, $1, $2, $3, ID_power); }
       | expr TOK_SLL expr { binary($$, $1, $2, $3, ID_shl); }
       | expr TOK_SRL expr { binary($$, $1, $2, $3, ID_lshr); }
       | expr TOK_SLA expr { binary($$, $1, $2, $3, ID_vhdl_sla); }
       | expr TOK_SRA expr { binary($$, $1, $2, $3, ID_ashr); }
       | expr TOK_ROL expr { binary($$, $1, $2, $3, ID_rol); }
       | expr TOK_ROR expr { binary($$, $1, $2, $3, ID_ror); }
       | expr TOK_AND expr  { binary($$, $1, $2, $3, ID_and); }
       | expr TOK_NAND expr { binary($$, $1, $2, $3, ID_nand); }
       | expr TOK_OR expr   { binary($$, $1, $2, $3, ID_or); }
       | expr TOK_NOR expr  { binary($$, $1, $2, $3, ID_nor); }
       | expr TOK_XOR expr  { binary($$, $1, $2, $3, ID_xor); }
       | expr TOK_XNOR expr { binary($$, $1, $2, $3, ID_xnor); }
       | expr '=' expr    { binary($$, $1, $2, $3, ID_equal); }
       | expr TOK_NE expr { binary($$, $1, $2, $3, ID_notequal); }
       | expr '<' expr    { binary($$, $1, $2, $3, ID_lt); }
       | expr TOK_LE expr { binary($$, $1, $2, $3, ID_le); }
       | expr '>' expr    { binary($$, $1, $2, $3, ID_gt); }
       | expr TOK_GE expr { binary($$, $1, $2, $3, ID_ge); }
       ;
