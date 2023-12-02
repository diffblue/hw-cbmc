%{
/*******************************************************************\

Module: Verilog Parser

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#include <cstdio>
#include <cstdlib>
#include <cstring>

#include <util/arith_tools.h>
#include <util/ebmc_util.h>
#include <util/mathematical_types.h>
#include <util/std_expr.h>

#include "verilog_parser.h"

#define PARSER verilog_parser
#define YYSTYPE unsigned
#define YYSTYPE_IS_TRIVIAL 1

//#define YYDEBUG 1

#define mto(x, y) stack_expr(x).add_to_operands(std::move(stack_expr(y)))
#define mts(x, y) stack_expr(x).move_to_sub((irept &)stack_expr(y))
#define swapop(x, y) stack_expr(x).operands().swap(stack_expr(y).operands())
#define addswap(x, y, z) stack_expr(x).add(y).swap(stack_expr(z))

int yyveriloglex();
extern char *yyverilogtext;

/*******************************************************************\

Function: init

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

inline static void init(exprt &expr)
{
  expr.clear();
  verilog_parser.set_source_location(expr);
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
  init(stack_expr(expr));
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
  stack_expr(expr).make_nil();
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
  stack_expr(expr).id(id);
}

/*******************************************************************\

Function: new_symbol

  Inputs:

 Outputs:

 Purpose:


\*******************************************************************/

inline static void new_symbol(YYSTYPE &dest, YYSTYPE &src)
{
  init(dest, ID_symbol);
  addswap(dest, ID_identifier, src);
}

/*******************************************************************\

Function: extractbit

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static void extractbit(YYSTYPE &expr, YYSTYPE &identifier, YYSTYPE &part)
{
  init(expr, ID_extractbit);
  mto(expr, identifier);
  stack_expr(expr).add_to_operands(std::move(to_unary_expr(stack_expr(part)).op()));
}

/*******************************************************************\

Function: extractbits

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static void extractbits(YYSTYPE &expr, YYSTYPE &identifier, YYSTYPE &range)
{
  init(expr, ID_extractbits);
  mto(expr, identifier);
  
  if(stack_expr(range).id()==ID_part_select)
  {
    auto &part_select = to_binary_expr(stack_expr(range));
    stack_expr(expr).add_to_operands(std::move(part_select.op0()));
    stack_expr(expr).add_to_operands(std::move(part_select.op1()));
  }
  else if(stack_expr(range).id()==ID_indexed_part_select_plus)
  {
    auto &part_select = to_binary_expr(stack_expr(range));
    exprt offset=minus_exprt(part_select.op1(), from_integer(1, integer_typet{}));
    stack_expr(expr).add_to_operands(part_select.op0());
    stack_expr(expr).add_to_operands(plus_exprt(part_select.op0(), offset));
  }
  else if(stack_expr(range).id()==ID_indexed_part_select_minus)
  {
    auto &part_select = to_binary_expr(stack_expr(range));
    exprt offset=minus_exprt(from_integer(1, integer_typet{}), part_select.op1());
    stack_expr(expr).add_to_operands(part_select.op0());
    stack_expr(expr).add_to_operands(plus_exprt(part_select.op0(), offset));
  }
  else
    PRECONDITION(false);
}

/*******************************************************************\

Function: add_as_subtype

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static void add_as_subtype(typet &dest, typet &what)
{
  // this is recursive and quadratic-time, so not super.
  if(what.is_nil())
  {
    // do nothing
  }
  else if(dest.is_nil() || dest.id()==irep_idt())
    dest.swap(what);
  else
  {
    typet &subtype=to_type_with_subtype(dest).subtype();
    add_as_subtype(subtype, what);
  }
}

/*******************************************************************\

Function: yyverilogerror

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int yyverilogerror(const char *error)
{
  verilog_parser.parse_error(error, yyverilogtext);
  return strlen(error)+1;
}

%}

/* Grammar Selection */
%token TOK_PARSE_LANGUAGE
%token TOK_PARSE_EXPRESSION
%token TOK_PARSE_TYPE

/* Generic */
%token TOK_PARENASTERIC     "(*"
%token TOK_ASTERICPAREN     "*)"

/* Unary */
%token TOK_EXCLAM           "!"
%token TOK_TILDE            "~"
%token TOK_AMPER            "&"
%token TOK_TILDEAMPER       "~&"
%token TOK_TILDEVERTBAR     "~|"
%token TOK_CARET            "^"
%token TOK_TILDECARET       "~^"
%token TOK_CARETTILDE       "^~"
%token TOK_MINUSGREATER     "->"

/* Binary */
%token TOK_ASTERIC          "*"
%token TOK_SLASH            "/"
%token TOK_PERCENT          "%"
%token TOK_EQUALEQUAL       "=="
%token TOK_EXCLAMEQUAL      "!="
%token TOK_EQUALEQUALEQUAL  "==="
%token TOK_EXCLAMEQUALEQUAL "!=="
%token TOK_AMPERAMPER       "&&"
%token TOK_ASTERICASTERIC   "**"
%token TOK_VERTBARVERTBAR   "||"
%token TOK_LESS             "<"
%token TOK_LESSEQUAL        "<="
%token TOK_GREATER          ">"
%token TOK_GREATEREQUAL     ">="
%token TOK_GREATERGREATER   ">>"
%token TOK_GREATERGREATERGREATER ">>>"
%token TOK_LESSLESS         "<<"
%token TOK_LESSLESSLESS     "<<<"

/* Unary or binary */
%token TOK_PLUS             "+"
%token TOK_MINUS            "-"
%token TOK_VERTBAR          "|"

/* Ternary */
%token TOK_QUESTION         "?"
%token TOK_COLON            ":"

/* Keywords */
%token TOK_ALWAYS           "always"
%token TOK_AND              "and"
%token TOK_ASSIGN           "assign"
%token TOK_AUTOMATIC        "automatic"
%token TOK_BEGIN            "begin"
%token TOK_BUF              "buf"
%token TOK_BUFIF0           "bufif0"
%token TOK_BUFIF1           "bufif1"
%token TOK_CASE             "case"
%token TOK_CASEX            "casex"
%token TOK_CASEZ            "casez"
%token TOK_CMOS             "cmos"
%token TOK_DEASSIGN         "deassign"
%token TOK_DEFAULT          "default"
%token TOK_DEFPARAM         "defparam"
%token TOK_DISABLE          "disable"
%token TOK_EDGE             "edge"
%token TOK_ELSE             "else"
%token TOK_END              "end"
%token TOK_ENDCASE          "endcase"
%token TOK_ENDFUNCTION      "endfunction"
%token TOK_ENDGENERATE      "endgenerate"
%token TOK_ENDMODULE        "endmodule"
%token TOK_ENDPRIMITIVE     "endprimitive"
%token TOK_ENDSPECIFY       "endspecify"
%token TOK_ENDTABLE         "endtable"
%token TOK_ENDTASK          "endtask"
%token TOK_EVENT            "event"
%token TOK_FOR              "for"
%token TOK_FORCE            "force"
%token TOK_FOREVER          "forever"
%token TOK_FORK             "fork"
%token TOK_FUNCTION         "function"
%token TOK_GENERATE         "generate"
%token TOK_GENVAR           "genvar"
%token TOK_HIGHZ0           "highz0"
%token TOK_HIGHZ1           "highz1"
%token TOK_IF               "if"
%token TOK_IFNONE           "ifnone"
%token TOK_INITIAL          "initial"
%token TOK_INOUT            "inout"
%token TOK_INPUT            "input"
%token TOK_INTEGER          "integer"
%token TOK_JOIN             "join"
%token TOK_LARGE            "large"
%token TOK_LOCALPARAM       "localparam"
%token TOK_MACROMODULE      "macromodule"
%token TOK_MEDIUM           "medium"
%token TOK_MODULE           "module"
%token TOK_NAND             "nand"
%token TOK_NEGEDGE          "negedge"
%token TOK_NMOS             "nmos"
%token TOK_NOR              "nor"
%token TOK_NOT              "not"
%token TOK_NOTIF0           "notif0"
%token TOK_NOTIF1           "notif1"
%token TOK_OR               "or"
%token TOK_OUTPUT           "output"
%token TOK_PARAMETER        "parameter"
%token TOK_PMOS             "pmos"
%token TOK_POSEDGE          "posedge"
%token TOK_PRIMITIVE        "primitive"
%token TOK_PULL0            "pull0"
%token TOK_PULL1            "pull1"
%token TOK_PULLDOWN         "pulldown"
%token TOK_PULLUP           "pullup"
%token TOK_RCMOS            "rcmos"
%token TOK_REAL             "real"
%token TOK_REALTIME         "realtime"
%token TOK_REG              "reg"
%token TOK_RELEASE          "release"
%token TOK_REPEAT           "repeat"
%token TOK_RNMOS            "rnmos"
%token TOK_RPMOS            "rpmos"
%token TOK_RTRAN            "rtran"
%token TOK_RTRANIF0         "rtranif0"
%token TOK_RTRANIF1         "rtranif1"
%token TOK_SCALARED         "scalared"
%token TOK_SIGNED           "signed"
%token TOK_SMALL            "small"
%token TOK_SPECIFY          "specify"
%token TOK_SPECPARAM        "specparam"
%token TOK_STRONG0          "strong0"
%token TOK_STRONG1          "strong1"
%token TOK_SUPPLY0          "supply0"
%token TOK_SUPPLY1          "supply1"
%token TOK_TABLE            "table"
%token TOK_TASK             "task"
%token TOK_TIME             "time"
%token TOK_TRAN             "tran"
%token TOK_TRANIF0          "tranif0"
%token TOK_TRANIF1          "tranif1"
%token TOK_TRI              "tri"
%token TOK_TRI0             "tri0"
%token TOK_TRI1             "tri1"
%token TOK_TRIAND           "triand"
%token TOK_TRIOR            "trior"
%token TOK_TRIREG           "trireg"
%token TOK_UNSIGNED         "unsigned"
%token TOK_VECTORED         "vectored"
%token TOK_WAIT             "wait"
%token TOK_WAND             "wand"
%token TOK_WEAK0            "weak0"
%token TOK_WEAK1            "weak1"
%token TOK_WHILE            "while"
%token TOK_WIRE             "wire"
%token TOK_WOR              "wor"
%token TOK_XNOR             "xnor"
%token TOK_XOR              "xor"
%token TOK_SETUP            "setup"
%token TOK_HOLD             "hold"
%token TOK_RECOVERY         "recovery"
%token TOK_REMOVAL          "removal"
%token TOK_WIDTH            "width"
%token TOK_SKEW             "skew"
%token TOK_UWIRE            "uwire"

/* System Verilog Operators */
%token TOK_VERTBARMINUSGREATER "|->"
%token TOK_VERTBAREQUALGREATER "|=>"
%token TOK_PLUSPLUS         "++"
%token TOK_MINUSMINUS       "--"
%token TOK_PLUSEQUAL        "+="
%token TOK_PLUSCOLON        "+:"
%token TOK_MINUSEQUAL       "-="
%token TOK_MINUSCOLON       "-:"
%token TOK_ASTERICEQUAL     "*="
%token TOK_SLASHEQUAL       "/="
%token TOK_PERCENTEQUAL     "%="
%token TOK_AMPEREQUAL       "&="
%token TOK_CARETEQUAL       "^="
%token TOK_VERTBAREQUAL     "|="
%token TOK_LESSLESSEQUAL    "<<="
%token TOK_GREATERGREATEREQUAL ">>="
%token TOK_LESSLESSLESSEQUAL "<<<="
%token TOK_GREATERGREATERGREATEREQUAL ">>>="
%token TOK_HASHHASH         "##"

/* System Verilog Keywords */
%token TOK_ACCEPT_ON        "accept_on"
%token TOK_ALIAS            "alias"
%token TOK_ALWAYS_COMB      "always_comb"
%token TOK_ALWAYS_FF        "always_ff"
%token TOK_ALWAYS_LATCH     "always_latch"
%token TOK_ASSERT           "assert"
%token TOK_ASSUME           "assume"
%token TOK_BEFORE           "before"
%token TOK_BIND             "bind"
%token TOK_BINS             "bins"
%token TOK_BINSOF           "binsof"
%token TOK_BIT              "bit"
%token TOK_BREAK            "break"
%token TOK_BYTE             "byte"
%token TOK_CHANDLE          "chandle"
%token TOK_CHECKER          "checker"
%token TOK_CLASS            "class"
%token TOK_CLOCKING         "clocking"
%token TOK_CONFIG           "config"
%token TOK_CONST            "const"
%token TOK_CONSTRAINT       "constraint"
%token TOK_CONTEXT          "context"
%token TOK_CONTINUE         "continue"
%token TOK_COVER            "cover"
%token TOK_COVERGROUP       "covergroup"
%token TOK_COVERPOINT       "coverpoint"
%token TOK_CROSS            "cross"
%token TOK_DIST             "dist"
%token TOK_DO               "do"
%token TOK_ENDCLASS         "endclass"
%token TOK_ENDCLOCKING      "endclocking"
%token TOK_ENDCONFIG        "endconfig"
%token TOK_ENDGROUP         "endgroup"
%token TOK_ENDINTERFACE     "endinterface"
%token TOK_ENDPACKAGE       "endpackage"
%token TOK_ENDPROGRAM       "endprogram"
%token TOK_ENDPROPERTY      "endproperty"
%token TOK_ENDSEQUENCE      "endsequence"
%token TOK_ENUM             "enum"
%token TOK_EVENTUALLY       "eventually"
%token TOK_EXPECT           "expect"
%token TOK_EXPORT           "export"
%token TOK_EXTENDS          "extends"
%token TOK_EXTERN           "extern"
%token TOK_FINAL            "final"
%token TOK_FIRST_MATCH      "first_match"
%token TOK_FOREACH          "foreach"
%token TOK_IFF              "iff"
%token TOK_IGNORE_BINS      "ignore_bins"
%token TOK_ILLEGAL_BINS     "illegal_bins"
%token TOK_IMPORT           "import"
%token TOK_INSIDE           "inside"
%token TOK_INT              "int"
%token TOK_INTERFACE        "interface"
%token TOK_INTERSECT        "intersect"
%token TOK_JOIN_ANY         "join_any"
%token TOK_JOIN_NONE        "join_none"
%token TOK_LOCAL            "local"
%token TOK_LOGIC            "logic"
%token TOK_LONGINT          "longint"
%token TOK_MATCHES          "matches"
%token TOK_MODPORT          "modport"
%token TOK_NEW              "new"
%token TOK_NEXTTIME         "nexttime"
%token TOK_NULL             "null"
%token TOK_PACKAGE          "package"
%token TOK_PACKED           "packed"
%token TOK_PRIORITY         "priority"
%token TOK_PROGRAM          "program"
%token TOK_PROPERTY         "property"
%token TOK_PROTECTED        "protected"
%token TOK_PURE             "pure"
%token TOK_RAND             "rand"
%token TOK_RANDC            "randc"
%token TOK_RANDCASE         "randcase"
%token TOK_RANDSEQUENCE     "randsequence"
%token TOK_REF              "ref"
%token TOK_RETURN           "return"
%token TOK_S_ALWAYS         "s_always"
%token TOK_S_EVENTUALLY     "s_eventually"
%token TOK_S_NEXTTIME       "s_nexttime"
%token TOK_S_UNTIL          "s_until"
%token TOK_S_UNTIL_WITH     "s_until_with"
%token TOK_SEQUENCE         "sequence"
%token TOK_SHORTINT         "shortint"
%token TOK_SHORTREAL        "shortreal"
%token TOK_SOLVE            "solve"
%token TOK_STATIC           "static"
%token TOK_STRING           "string"
%token TOK_STRUCT           "struct"
%token TOK_SUPER            "super"
%token TOK_TAGGED           "tagged"
%token TOK_THIS             "this"
%token TOK_THROUGHOUT       "throughout"
%token TOK_TIMEPRECISION    "timeprecision"
%token TOK_TIMEUNIT         "timeunit"
%token TOK_TYPE             "type"
%token TOK_TYPEDEF          "typedef"
%token TOK_UNION            "union"
%token TOK_UNIQUE           "unique"
%token TOK_UNTIL            "until"
%token TOK_UNTIL_WITH       "until_with"
%token TOK_VAR              "var"
%token TOK_VIRTUAL          "virtual"
%token TOK_VOID             "void"
%token TOK_WAIT_ORDER       "wait_order"
%token TOK_WILDCARD         "wildcard"
%token TOK_WITH             "with"
%token TOK_WITHIN           "within"

/* Others */
%token TOK_ENDOFFILE
%token TOK_CHARSTR
%token TOK_NUMBER           // number, any base
%token TOK_TIME_LITERAL     // number followed by time unit
%token TOK_QSTRING          // quoted string
%token TOK_SYSIDENT         // system task or function enable
%token TOK_SCANNER_ERROR

// Precedence of System Verilog Assertions Operators,
// following System Verilog 1800-2017 Table 16-3.
// Bison expects these in order of increasing precedence,
// whereas the table gives them in decreasing order.
// The precendence of the assertion operators is lower than
// those in Table 11-2.
%nonassoc "always" "s_always" "eventually" "s_eventually"
%nonassoc "accept_on" "reject_on"
%nonassoc "sync_accept_on" "sync_reject_on"
%right "|->" "|=>" "#-#" "#=#"
%nonassoc "until" "s_until" "until_with" "s_until_with" "implies"
%right "iff"
%left "or"
%left "and"
%nonassoc "not" "nexttime" "s_nexttime"
%left "##"
%nonassoc "[*]" "[=]" "[->]"

// Precendence of Verilog operators,
// following System Verilog 1800-2017 Table 11-2.
// Bison expects these in order of increasing precedence,
// whereas the table gives them in decreasing order.
%right "->" "<->"
%right "?" ":"
%left "||"
%left "&&"
%left "|"
%left "^" "^~" "~^"
%left "&"
%left "==" "!=" "===" "!==" "==?" "!=?"
%left "<" "<=" ">" ">=" "inside" "dist"
%left "<<" ">>" "<<<" ">>>"
%left "+" "-"
%left "*" "/" "%"
%left "**"
%nonassoc UNARY_PLUS UNARY_MINUS "!" "~" "&~" "++" "--"

// Statements
%nonassoc LT_TOK_ELSE
%nonassoc TOK_ELSE

%%

/* Starting point */

grammar:  TOK_PARSE_LANGUAGE { /*yydebug=1;*/ } source_text
        | TOK_PARSE_EXPRESSION expression
           { PARSER.parse_tree.expr.swap(stack_expr($2)); }
        | TOK_PARSE_TYPE data_type_or_implicit
           { PARSER.parse_tree.expr.swap(stack_expr($2)); }
        ;

// System Verilog standard 1800-2017
// A.1.2 SystemVerilog source text

source_text: description_brace;

description_brace:
          /* Optional */
	| description_brace description
	;

description:
	  module_declaration
	| udp_declaration
	| interface_declaration
 	| program_declaration
 	| package_declaration
 	| attribute_instance_brace bind_directive
 	| config_declaration
 	| type_declaration
          { PARSER.parse_tree.create_typedef(stack_expr($1)); }
        ;

/*
 	| attribute_instance_brace package_item
*/

module_nonansi_header:
	  attribute_instance_brace
	  module_keyword
	  module_identifier
	  parameter_port_list_opt
	  list_of_ports_opt ';'
          {
            init($$); stack_expr($$).operands().resize(5);
            stack_expr($$).operands()[0].swap(stack_expr($1));
            stack_expr($$).operands()[1].swap(stack_expr($2));
            stack_expr($$).operands()[2].swap(stack_expr($3));
            stack_expr($$).operands()[3].swap(stack_expr($4));
            stack_expr($$).operands()[4].swap(stack_expr($5));
          }
        ;

module_ansi_header:
          attribute_instance_brace
	  module_keyword
	  module_identifier
	  parameter_port_list_opt
	  list_of_port_declarations ';'
          {
            init($$); stack_expr($$).operands().resize(5);
            stack_expr($$).operands()[0].swap(stack_expr($1));
            stack_expr($$).operands()[1].swap(stack_expr($2));
            stack_expr($$).operands()[2].swap(stack_expr($3));
            stack_expr($$).operands()[3].swap(stack_expr($4));
            stack_expr($$).operands()[4].swap(stack_expr($5));
          }
        ;

module_declaration:
          module_nonansi_header module_item_brace TOK_ENDMODULE module_identifier_opt
          {
            PARSER.parse_tree.create_module(
              stack_expr($1).operands()[0],
              stack_expr($1).operands()[1],
              stack_expr($1).operands()[2],
              stack_expr($1).operands()[3],
              stack_expr($1).operands()[4],
              stack_expr($2));
          }
        | module_ansi_header module_item_brace TOK_ENDMODULE module_identifier_opt
          {
            PARSER.parse_tree.create_module(
              stack_expr($1).operands()[0],
              stack_expr($1).operands()[1],
              stack_expr($1).operands()[2],
              stack_expr($1).operands()[3],
              stack_expr($1).operands()[4],
              stack_expr($2));
          }
        | TOK_EXTERN module_nonansi_header
          /* ignored for now */
        | TOK_EXTERN module_ansi_header
          /* ignored for now */
	;

module_keyword:
	  TOK_MODULE { init($$, ID_module); }
	| TOK_MACROMODULE { init($$, ID_macromodule); }
	;

interface_declaration:
          TOK_INTERFACE TOK_ENDINTERFACE
        ;

program_declaration:
          TOK_PROGRAM TOK_ENDPROGRAM
        ;

package_declaration:
          TOK_PACKAGE TOK_ENDPACKAGE
        ;

// System Verilog standard 1800-2017
// A.1.3 Module parameters and ports

// This deviates from the grammar in the standard to address an
// ambiguity between the comma in list_of_param_assignments
// and the comma in parameter_port_list. The productions
// allowed by list_of_param_assignments are folded into
// parameter_port_declaration.
parameter_port_list_opt:
	 /* Optional */
	        { init($$); }
        | '#' '(' parameter_port_declaration_brace ')'
	        { $$ = $3; }
        | '#' '(' ')'
	        { init($$); }
	;

list_of_ports: '(' port_brace ')' { $$ = $2; }
	;

port_declaration_brace:
	  module_port_declaration
		{ init($$); mts($$, $1); }
	| port_declaration_brace ',' module_port_declaration
		{ $$=$1; mts($$, $3); }

          // append to last one -- required to make 
          // the grammar LR1
	| port_declaration_brace ',' port_identifier
		{ $$=$1;
		  exprt decl(ID_decl);
		  decl.add_to_operands(std::move(stack_expr($3)));
		  // grab the type and class from previous!
		  const irept &prev=stack_expr($$).get_sub().back();
                  decl.set(ID_type, prev.find(ID_type));
                  decl.set(ID_class, prev.find(ID_class));
		  stack_expr($$).move_to_sub(decl);
		}
	;

port_declaration:
	  attribute_instance_brace inout_declaration { $$=$2; }
	| attribute_instance_brace input_declaration { $$=$2; }
	| attribute_instance_brace output_declaration { $$=$2; }
	;

module_port_declaration:
	  attribute_instance_brace module_port_inout_declaration { $$=$2; }
	| attribute_instance_brace module_port_input_declaration { $$=$2; }
	| attribute_instance_brace module_port_output_declaration { $$=$2; }
	;

module_port_input_declaration:
	  TOK_INPUT port_type port_identifier
		{ init($$, ID_decl);
                  stack_expr($$).set(ID_class, ID_input);
                  addswap($$, ID_type, $2);
                  mto($$, $3); }
	;

module_port_output_declaration:
	  TOK_OUTPUT port_type port_identifier
		{ init($$, ID_decl);
                  stack_expr($$).set(ID_class, ID_output);
                  addswap($$, ID_type, $2);
                  mto($$, $3); }
	| TOK_OUTPUT data_type port_identifier
		{ init($$, ID_decl);
                  stack_expr($$).set(ID_class, ID_output_register);
                  addswap($$, ID_type, $2);
                  mto($$, $3); }
	;

// System Verilog standard 1800-2017
// A.1.4 Module items

module_common_item:
          module_or_generate_item_declaration
        | bind_directive
	| continuous_assign
	| initial_construct
	| always_construct
        ;

module_item:
	  port_declaration ';'
        | non_port_module_item
        ;

module_item_brace:
		/* Optional */
		{ init($$); }
	| module_item_brace module_item
		{ $$=$1; mts($$, $2); }
	;

module_or_generate_item:
	  attribute_instance_brace parameter_override { $$=$2; }
	| attribute_instance_brace gate_instantiation { $$=$2; }
	// | attribute_instance_brace udp_instantiation { $$=$2; }
	| attribute_instance_brace module_instantiation { $$=$2; }
	| attribute_instance_brace concurrent_assert_statement { $$=$2; }
	| attribute_instance_brace concurrent_assume_statement { $$=$2; }
	| attribute_instance_brace concurrent_cover_statement { $$=$2; }
	| attribute_instance_brace concurrent_assertion_item_declaration { $$=$2; }
	| attribute_instance_brace module_common_item { $$=$2; }
	;

module_or_generate_item_declaration:
          package_or_generate_item_declaration
	| genvar_declaration
	;

non_port_module_item:
	  attribute_instance_brace generate_region { $$=$2; }
        | module_or_generate_item
        | attribute_instance_brace specparam_declaration {$$=$2; }
	| attribute_instance_brace specify_block { $$=$2;}
        ;

/*
	  module_or_generate_item
	| attribute_instance_brace parameter_declaration { $$=$2; }
	// | attribute_instance_brace local_parameter_declaration { $$=$2; }
	;
*/

// System Verilog standard 1800-2017
// A.1.5 Configuration source text

config_declaration:
          TOK_CONFIG TOK_ENDCONFIG
        ;

bind_directive:
          TOK_BIND
        ;
	
// System Verilog standard 1800-2017
// A.1.11 Package items

package_item:
        ;

// System Verilog standard 1800-2017
// A.2.1.1 Module parameter declarations

local_parameter_declaration:
          TOK_LOCALPARAM data_type_or_implicit list_of_param_assignments
		{ init($$, ID_local_parameter_decl); swapop($$, $3); }
	;

parameter_declaration:
          TOK_PARAMETER data_type_or_implicit list_of_param_assignments
		{ init($$, ID_parameter_decl); swapop($$, $3); }
	;

specparam_declaration:
	  TOK_SPECPARAM data_type_or_implicit list_of_specparam_assignments ';'
	;

// System Verilog standard 1800-2017
// A.2.1.2 Port declarations

module_port_inout_declaration:
	  TOK_INOUT port_type port_identifier
		{ init($$, ID_decl);
                  stack_expr($$).set(ID_class, ID_inout);
                  addswap($$, ID_type, $2);
                  mto($$, $3); }
	;

port_brace:
	  port
		{ init($$); mts($$, $1); }
	| port_brace ',' port
		{ $$=$1;    mts($$, $3); }
	;

port:	  port_expression_opt
		{ if(stack_expr($1).is_nil())
		    $$=$1;
		  else { init($$, ID_decl);  mto($$, $1); }
		}
	| '.' port_identifier '(' port_expression_opt ')'
		{ init($$, ID_decl);
		  make_nil($$); /* Not supported */ }
	;

port_expression_opt:
	  /* Optional */
	  { make_nil($$); }
	| port_reference
	;

port_reference:
	  port_identifier
	| port_identifier bit_select  { make_nil($$); /* Not supported */ }
	| port_identifier part_select { make_nil($$); /* Not supported */ }
	;

bit_select:
	  '[' expression ']'
		{ init($$, ID_bit_select); mto($$, $2); }
	;

part_select:
	  '[' const_expression TOK_COLON const_expression ']'
		{ init($$, ID_part_select); mto($$, $2); mto($$, $4); }
	;

indexed_part_select:
	  '[' const_expression TOK_PLUSCOLON const_expression ']'
		{ init($$, ID_indexed_part_select_plus); mto($$, $2); mto($$, $4); }
        | '[' const_expression TOK_MINUSCOLON const_expression ']'
		{ init($$, ID_indexed_part_select_minus); mto($$, $2); mto($$, $4); }
	;

// System Verilog standard 1800-2017
// A.2.1.3 Type declarations

// TOK_VAR is optional, but footnote 10 in IEEE 1800-2017 requires it
// when the data_type is omitted. We split the rule in the standard into two.
data_declaration:
	  TOK_VAR lifetime_opt data_type_or_implicit list_of_variable_decl_assignments ';'
	  	{ init($$, ID_decl);
		  stack_expr($$).set(ID_class, ID_var);
		  addswap($$, ID_type, $3);
		  swapop($$, $4); }
	| lifetime_opt data_type list_of_variable_decl_assignments ';'
		{ init($$, ID_decl);
		  stack_expr($$).set(ID_class, ID_reg);
		  addswap($$, ID_type, $2);
		  swapop($$, $3); }
	| type_declaration
	;

genvar_declaration:
	  TOK_GENVAR list_of_genvar_identifiers ';'
		{ init($$, ID_decl); stack_expr($$).set(ID_class, ID_genvar); swapop($$, $2); }
	;

net_declaration:
          net_type drive_strength_opt vectored_scalared_opt data_type_or_implicit delay3_opt list_of_net_names ';'
		{ init($$, ID_decl);
                  addswap($$, ID_class, $1);
                  addswap($$, ID_type, $4);
                  swapop($$, $6); }
        | net_type drive_strength_opt vectored_scalared_opt data_type_or_implicit delay3_opt list_of_net_decl_assignments ';'
		{ init($$, ID_decl);
                  addswap($$, ID_class, $1);
                  addswap($$, ID_type, $4);
                  swapop($$, $6); }
	;

type_declaration:
	  TOK_TYPEDEF data_type type_identifier ';'
		{ init($$, ID_decl);
		  stack_expr($$).set(ID_class, ID_typedef);
		  addswap($$, ID_type, $2);
		  mto($$, $3);
		}
	;

vectored_scalared_opt:
          /* Optional */
                { make_nil($$); }
	| TOK_VECTORED     { init($$, "vectored"); }
	| TOK_SCALARED     { init($$, "scalared"); }
	;

list_of_net_names:
	  net_name
		{ init($$); mto($$, $1); }
	| list_of_net_names ',' net_name
		{ $$=$1;    mto($$, $3); }
	;

net_name: net_identifier packed_dimension_brace
          {
            $$=$1;
            stack_expr($$).add(ID_type)=stack_expr($2);
          }
	;

list_of_net_decl_assignments:
	  net_decl_assignment
		{ init($$); mto($$, $1); }
	| list_of_net_decl_assignments ',' net_decl_assignment
		{ $$=$1;    mto($$, $3); }
	;

lifetime_opt:
	  /* optional */
	| lifetime
	;

lifetime:
	  TOK_STATIC { init($$, ID_static); }
	| TOK_AUTOMATIC { init($$, ID_automatic); }
	;

// System Verilog standard 1800-2017
// A.2.2.1 Net and variable types

data_type:
	  integer_vector_type signing_opt packed_dimension_brace
	        {
                  $$=$3;
                  add_as_subtype(stack_type($$), stack_type($2));
                }
	| integer_atom_type signing_opt
	        {
                  $$=$1;
                  add_as_subtype(stack_type($$), stack_type($2));
                }
	| non_integer_type
	| struct_union packed_opt signing_opt 
	  '{' struct_union_member_list '}' packed_dimension_brace
	        { /* todo */ }
	| TOK_ENUM enum_base_type_opt '{' enum_name_declaration_list '}'
	        { init($$, ID_c_enum); }
	| TOK_STRING
	        { init($$, ID_string); }
	| TOK_CHANDLE
	        { init($$, ID_chandle); }
	| TOK_VIRTUAL interface_opt interface_identifier
	        { init($$, "virtual_interface"); }
	/*
	| scope_opt type_identifier packed_dimension_brace
	*/
	| class_type
	| TOK_EVENT
	        { init($$, ID_event); }
	/*
	| ps_covergroup_identifier
	*/
	;
	
enum_name_declaration:
	  TOK_CHARSTR
	;
	
enum_name_declaration_list:
          enum_name_declaration
          	{ init($$); mts($$, $1); }
        | enum_name_declaration_list ',' enum_name_declaration
          	{ $$=$1; mts($$, $3); }
	;
	
integer_vector_type:
          TOK_BIT { init($$, ID_verilog_bit); }
        | TOK_LOGIC { init($$, ID_verilog_logic); }
        | TOK_REG { init($$, ID_reg); }
	;
	
integer_atom_type:
	  TOK_BYTE { init($$, ID_verilog_byte); }
	| TOK_SHORTINT { init($$, ID_verilog_shortint); }
	| TOK_INT { init($$, ID_verilog_int); }
	| TOK_LONGINT { init($$, ID_verilog_longint); }
	| TOK_INTEGER { init($$, ID_integer); }
	| TOK_TIME { init($$, ID_verilog_time); }
	;
	
class_type: TOK_CLASS
                { init($$, ID_class); }
	;
	
struct_union_member_list:
	;
	
enum_base_type_opt:
	;

non_integer_type:
	  TOK_SHORTREAL
		{ init($$, ID_verilog_shortreal); }
	| TOK_REAL
		{ init($$, ID_verilog_real); }
	| TOK_REALTIME
		{ init($$, ID_verilog_realtime); }
	;

net_type: TOK_SUPPLY0 { init($$, ID_supply0); }
	| TOK_SUPPLY1 { init($$, ID_supply1); }
	| TOK_TRI     { init($$, ID_tri); }
	| TOK_TRIAND  { init($$, ID_triand); }
	| TOK_TRIOR   { init($$, ID_trior); }
	| TOK_TRIREG  { init($$, ID_trireg); }
	| TOK_TRI0    { init($$, ID_tri0); }
	| TOK_TRI1    { init($$, ID_tri1); }
	| TOK_UWIRE   { init($$, ID_uwire); }
	| TOK_WIRE    { init($$, ID_wire); }
	| TOK_WAND    { init($$, ID_wand); }
	| TOK_WOR     { init($$, ID_wor); }
	;

interface_opt:
	  /* Optional */
	  { make_nil($$); }
	| TOK_INTERFACE { init($$, ID_interface); }
	;
	
scope_opt:
          /* Optional */
          { make_nil($$); }
        | scope
        ;

scope:
	;
	
packed_opt:
	  /* Optional */
	  { make_nil($$); }
	| TOK_PACKED { init($$, ID_packed); }
	;

packed_dimension_brace:
	  /* Optional */
	  { make_nil($$); }
	| packed_dimension_brace packed_dimension
	  {
	    $$=$1;
	    add_as_subtype(stack_type($$), stack_type($2));
	  }
	;

// System Verilog standard 1800-2017
// A.2.2.2 Strengths

drive_strength_opt:
	  /* Optional */ { make_nil($$); }
//	| drive_strength
	;

/*
drive_strength:
	  '(' strength0 ',' strength1 ')'
	| '(' strength1 ',' strength0 ')'
	| '(' strength0 ',' TOK_HIGHZ1  ')'
	| '(' strength1 ',' TOK_HIGHZ0  ')'
	| '(' TOK_HIGHZ0  ',' strength1 ')'
	| '(' TOK_HIGHZ1  ',' strength0 ')'
	;

strength0:
	  TOK_SUPPLY0
	| TOK_STRONG0
	| TOK_PULL0
	| TOK_WEAK0
	;

strength1:
	  TOK_SUPPLY1
	| TOK_STRONG1
	| TOK_PULL1
	| TOK_WEAK1
	;
*/

charge_strength:
	  '(' TOK_SMALL ')'
	| '(' TOK_MEDIUM ')'
	| '(' TOK_LARGE ')'
	;

charge_strength_opt:
          /* Optional */
                { make_nil($$); }
	| charge_strength
	;

// System Verilog standard 1800-2017
// A.2.2.3 Delays

delay3_opt:
		{ make_nil($$); }
	| delay3
	;

delay3:   '#' delay_value { $$=$2; }
	| '#' '(' delay_value ')' { $$=$3; }
	| '#' '(' delay_value ',' delay_value ')' { $$=$3; }
	| '#' '(' delay_value ',' delay_value ',' delay_value ')' { $$=$3; }
	;

delay_value:
          unsigned_number
	| variable_identifier
	| time_literal
        ;

// System Verilog standard 1800-2017
// A.2.3 Declaration lists

list_of_genvar_identifiers:
	  genvar_identifier
		{ init($$); mto($$, $1); } 
	| list_of_genvar_identifiers ',' genvar_identifier
		{ $$=$1;    mto($$, $3); }
	;

defparam_assignment:
	  hierarchical_parameter_identifier '=' constant_expression
		{ init($$, ID_parameter_assignment); mto($$, $1); mto($$, $3); }
	;

parameter_port_declaration_brace:
	  parameter_port_declaration
		{ init($$, ID_parameter_decl); mto($$, $1); }
	| parameter_port_declaration_brace ',' parameter_port_declaration
		{ $$=$1; mto($$, $3); }
	;

list_of_variable_decl_assignments:
	  variable_decl_assignment
		{ init($$); mto($$, $1); }
	| list_of_variable_decl_assignments ',' variable_decl_assignment
		{ $$=$1;    mto($$, $3); }
	;

// This rule is more permissive that the grammar in the standard
// to cover list_of_param_assignments.
parameter_port_declaration:
          TOK_PARAMETER param_assignment
		{ $$ = $2; }
	| data_type param_assignment
		{ $$ = $2; }
	| param_assignment
	;

list_of_defparam_assignments:
	  defparam_assignment
		{ init($$); mto($$, $1); }
	| list_of_defparam_assignments ',' defparam_assignment
		{ $$=$1;    mto($$, $3); }
	;

parameter_override:
	  TOK_DEFPARAM list_of_defparam_assignments ';'
		{ init($$, ID_parameter_override); swapop($$, $2); }
	;

list_of_param_assignments:
	  param_assignment
		{ init($$); mto($$, $1); }
	| list_of_param_assignments ',' param_assignment
		{ $$=$1;    mto($$, $3); }
	;

param_assignment: param_identifier '=' const_expression
		{ init($$, ID_parameter);
		  addswap($$, ID_identifier, $1);
		  addswap($$, ID_value, $3); }
        ;

data_type_or_implicit:
           data_type
        |  implicit_data_type
        ;

implicit_data_type:
          signing_opt packed_dimension_brace
                {
                  $$=$2;
                  add_as_subtype(stack_type($$), stack_type($1));
                }
        ;

input_declaration:
	  TOK_INPUT port_type list_of_port_identifiers
		{ init($$, ID_decl);
                  stack_expr($$).set(ID_class, ID_input);
                  addswap($$, ID_type, $2);
                  swapop($$, $3); }
	;

output_declaration:
	  TOK_OUTPUT port_type list_of_port_identifiers
		{ init($$, ID_decl);
                  stack_expr($$).set(ID_class, ID_output);
                  addswap($$, ID_type, $2);
                  swapop($$, $3); }
	| TOK_OUTPUT data_type list_of_port_identifiers
		{ init($$, ID_decl);
                  stack_expr($$).set(ID_class, ID_output_register);
                  addswap($$, ID_type, $2);
                  swapop($$, $3); }
	;

inout_declaration:
	  TOK_INOUT port_type list_of_port_identifiers
		{ init($$, ID_decl);
                  stack_expr($$).set(ID_class, ID_inout);
                  addswap($$, ID_type, $2);
                  swapop($$, $3); }
	;

port_type: net_type_opt signing_opt packed_dimension_brace
                {
                  $$=$3;
                  add_as_subtype(stack_type($$), stack_type($2));
                  // the net type is ignored right now
                }
        ;
        
net_type_opt:
          /* Optional */
                { init($$, ID_nil); }
        | net_type
        ;

signing_opt:
	  /* Optional */
	        { make_nil($$); } 
	| signing
	;

signing:
	  TOK_SIGNED { init($$, ID_signed); }
	| TOK_UNSIGNED { init($$, ID_unsigned); }
	;

automatic_opt:
	  /* Optional */
	        { make_nil($$); } 
	| TOK_AUTOMATIC
	        { init($$, ID_automatic); }
	;

list_of_port_identifiers:
	  port_identifier unpacked_dimension_brace
		{ init($$); stack_expr($1).type().swap(stack_expr($2)); mto($$, $1); }
	| list_of_port_identifiers ',' port_identifier unpacked_dimension_brace
		{ $$=$1;    stack_expr($3).type().swap(stack_expr($4)); mto($$, $3); }
	;

range_opt:
                { make_nil($$); }
	| range
	;

range:	part_select;

// System Verilog standard 1800-2017
// A.2.4 Declaration assignments

net_decl_assignment: net_identifier '=' expression
		{ init($$, ID_equal); mto($$, $1); mto($$, $3); }
	;

variable_decl_assignment:
	  variable_identifier variable_dimension_brace
		{ $$ = $1; stack_expr($$).type().swap(stack_expr($2)); }
	| variable_identifier variable_dimension_brace '=' expression
		{ init($$, ID_equal);
		  stack_expr($1).type().swap(stack_expr($2));
		  mto($$, $1);
		  mto($$, $4); }
	;

// System Verilog standard 1800-2017
// A.2.5 Declaration ranges

unpacked_dimension_brace:
	  /* Optional */
	  { make_nil($$); }
	| unpacked_dimension_brace unpacked_dimension
	  {
	    $$=$1;
	    add_as_subtype(stack_type($$), stack_type($2));
	  }
	;

packed_dimension:
	  '[' const_expression TOK_COLON const_expression ']'
		{ init($$, ID_array);
		  stack_type($$).add_subtype().make_nil();
		  exprt &range=static_cast<exprt &>(stack_type($$).add(ID_range));
		  range.add_to_operands(stack_expr($2));
		  range.add_to_operands(stack_expr($4)); }
	| unsized_dimension
	;

unpacked_dimension:
	  '[' const_expression TOK_COLON const_expression ']'
		{ init($$, ID_array);
		  stack_type($$).add_subtype().make_nil();
		  exprt &range=static_cast<exprt &>(stack_type($$).add(ID_range));
		  range.add_to_operands(stack_expr($2));
		  range.add_to_operands(stack_expr($4)); }
	| '[' expression ']'
	{
	  $$=$2;
	}
	;

variable_dimension:
	  unsized_dimension
	| unpacked_dimension
	;

variable_dimension_brace:
	  /* Optional */
	  { make_nil($$); }
	| variable_dimension_brace variable_dimension
	  {
	    $$=$1;
	    add_as_subtype(stack_type($$), stack_type($2));
	  }
	;

unsized_dimension: '[' ']'
                { init($$, "unsized"); }
	;

struct_union:
	  TOK_STRUCT { init($$, ID_struct); }
	| TOK_UNION { init($$, ID_union); }
	;
	
// System Verilog standard 1800-2017
// A.2.6 Function declarations

function_declaration:
	  TOK_FUNCTION automatic_opt signing_opt range_or_type_opt
	  function_identifier list_of_ports_opt ';'
          function_item_declaration_brace statement TOK_ENDFUNCTION
		{ init($$, ID_decl);
                  stack_expr($$).set(ID_class, ID_function); 
                  addswap($$, ID_type, $4);
                  add_as_subtype(stack_type($4), stack_type($3));
                  addswap($$, ID_symbol, $5);
		  addswap($$, ID_ports, $6);
		  addswap($$, "declarations", $8);
		  addswap($$, ID_body, $9);
		}
	;

range_or_type_opt:
	  /* Optional */
		{ make_nil($$); }
	| range_or_type
		{ $$ = $1; }
	;

range_or_type:
	  packed_dimension
	| TOK_INTEGER
		{ init($$, ID_integer); }
	| TOK_REAL
		{ init($$, ID_verilog_real); }
	| TOK_REALTIME
		{ init($$, ID_verilog_realtime); }
	| TOK_TIME
		{ init($$, ID_verilog_time); }
	;

function_item_declaration_brace:
	  function_item_declaration
		{ init($$); mts($$, $1); }
	| function_item_declaration_brace function_item_declaration
		{ $$=$1; mts($$, $2); }
	;

function_item_declaration:
	  block_item_declaration
	| input_declaration ';'
	;

// System Verilog standard 1800-2017
// A.2.7 Task declarations

task_declaration:
	  TOK_TASK task_identifier list_of_ports_opt ';'
	  task_item_declaration_brace
	  statement_or_null TOK_ENDTASK
		{ init($$, ID_decl);
                  stack_expr($$).set(ID_class, ID_task); 
		  addswap($$, ID_symbol, $2);
		  addswap($$, ID_ports, $3);
		  addswap($$, "declarations", $5);
		  addswap($$, ID_body, $6);
                }
	;

task_item_declaration_brace:
	  /* Optional */
		{ init($$); }
	| task_item_declaration_brace task_item_declaration
		{ $$=$1; mts($$, $2); }
	;

task_item_declaration:
	  block_item_declaration
	| attribute_instance_brace input_declaration  ';' { $$=$2; }
	| attribute_instance_brace output_declaration ';' { $$=$2; }
	| attribute_instance_brace inout_declaration  ';' { $$=$2; }
	;

// System Verilog standard 1800-2017
// A.2.8 Block item declarations

block_item_declaration:
	  attribute_instance_brace data_declaration { $$=$2; }
	| attribute_instance_brace local_parameter_declaration ';' { $$=$2; }
	| attribute_instance_brace parameter_declaration ';' { $$=$2; }
	;

// System Verilog standard 1800-2017
// A.2.10 Assertion declarations

concurrent_assertion_item_declaration:
	  property_declaration
	;

assert_property_statement:
          TOK_ASSERT TOK_PROPERTY '(' property_expr ')' action_block
		{ init($$, ID_assert); mto($$, $4); mto($$, $6); }
	| /* this one is in because SMV does it */
	  TOK_ASSERT property_identifier TOK_COLON expression ';'
		{ init($$, ID_assert); stack_expr($$).operands().resize(2);
		  to_binary_expr(stack_expr($$)).op0().swap(stack_expr($4));
		  to_binary_expr(stack_expr($$)).op1().make_nil();
		  stack_expr($$).set(ID_identifier, stack_expr($2).id());
		}
	;

assume_property_statement:
          TOK_ASSUME TOK_PROPERTY '(' property_expr ')' action_block
		{ init($$, ID_assume); mto($$, $4); mto($$, $6); }
	| /* this one is in because SMV does it */
	  TOK_ASSUME property_identifier TOK_COLON expression ';'
		{ init($$, ID_assume); stack_expr($$).operands().resize(2);
		  to_binary_expr(stack_expr($$)).op0().swap(stack_expr($4));
		  to_binary_expr(stack_expr($$)).op1().make_nil();
		  stack_expr($$).set(ID_identifier, stack_expr($2).id());
		}
	;

cover_property_statement: TOK_COVER TOK_PROPERTY '(' expression ')' action_block
		{ init($$, ID_cover); mto($$, $4); mto($$, $6); }
	;

property_declaration:
          TOK_PROPERTY property_identifier TOK_ENDPROPERTY
        ;

property_expr:
          sequence_expr
        | "not" property_expr               { init($$, ID_not); mto($$, $2); }
        | property_expr "or" property_expr  { init($$, ID_or); mto($$, $1); mto($$, $3); }
        | property_expr "and" property_expr { init($$, ID_and); mto($$, $1); mto($$, $3); }
        | property_expr "|->" property_expr { init($$, ID_sva_overlapped_implication); mto($$, $1); mto($$, $3); }
        | property_expr "|=>" property_expr { init($$, ID_sva_non_overlapped_implication); mto($$, $1); mto($$, $3); }
        | "nexttime" property_expr          { init($$, "sva_nexttime"); mto($$, $2); }
        | "s_nexttime" property_expr        { init($$, "sva_s_nexttime"); mto($$, $2); }
        | "always" property_expr            { init($$, "sva_always"); mto($$, $2); }
        | "s_always" property_expr          { init($$, "sva_s_always"); mto($$, $2); }
        | "s_eventually" property_expr      { init($$, "sva_s_eventually"); mto($$, $2); }
        | "eventually" property_expr        { init($$, "sva_eventually"); mto($$, $2); }
        | property_expr "until" property_expr        { init($$, "sva_until"); mto($$, $1); mto($$, $3); }
        | property_expr "until_with" property_expr   { init($$, "sva_until_with"); mto($$, $1); mto($$, $3); }
        | property_expr "s_until" property_expr      { init($$, "sva_s_until"); mto($$, $1); mto($$, $3); }
        | property_expr "s_until_with" property_expr { init($$, "sva_s_until_with"); mto($$, $1); mto($$, $3); }
//        | property_expr "implies" property_expr       { init($$, ID_implies); mto($$, $1); mto($$, $3); }
//        | property_expr "iff" property_expr           { init($$, ID_iff); mto($$, $1); mto($$, $3); }
        | "accept_on" '(' expression_or_dist ')'      { init($$, "sva_accept_on"); mto($$, $3); }
        | "reject_on" '(' expression_or_dist ')'      { init($$, "sva_reject_on"); mto($$, $3); }
        | "sync_accept_on" '(' expression_or_dist ')' { init($$, "sva_sync_accept_on"); mto($$, $3); }
        | "sync_reject_on" '(' expression_or_dist ')' { init($$, "sva_sync_reject_on"); mto($$, $3); }
        | event_control '(' property_expr ')' { $$=$3; }
        ;

sequence_expr:
          expression
        | cycle_delay_range sequence_expr
                { $$=$1; mto($$, $2); }
        | expression cycle_delay_range sequence_expr
                { init($$, ID_sva_sequence_concatenation); mto($$, $1); mto($2, $3); mto($$, $2); }
        | "first_match" '(' sequence_expr ')'
                { init($$, ID_sva_sequence_first_match); mto($$, $3); }
        | expression "throughout" sequence_expr
                { init($$, ID_sva_sequence_throughout); mto($$, $1); mto($$, $3); }
        ;

cycle_delay_range:
          "##" number
                { init($$, ID_sva_cycle_delay); mto($$, $2); stack_expr($$).operands().push_back(nil_exprt()); }
        | "##" '[' number TOK_COLON number ']'
                { init($$, ID_sva_cycle_delay); mto($$, $3); mto($$, $5); }
        | "##" '[' number TOK_COLON '$' ']'
                { init($$, ID_sva_cycle_delay); mto($$, $3); stack_expr($$).add_to_operands(exprt(ID_infinity)); }
        ;

expression_or_dist:
	  expression
	;

// System Verilog standard 1800-2017
// A.3.1 Primitive instantiation and instances

gate_instantiation:
	  cmos_switchtype delay3_opt gate_instance_brace ';'
		{ init($$, ID_inst_builtin); addswap($$, ID_module, $1); swapop($$, $3); }
	| enable_gatetype drive_strength_opt delay3_opt gate_instance_brace ';'
		{ init($$, ID_inst_builtin); addswap($$, ID_module, $1); swapop($$, $4); }
	| mos_switchtype delay3_opt gate_instance_brace ';'
		{ init($$, ID_inst_builtin); addswap($$, ID_module, $1); swapop($$, $3); }
	| n_input_gatetype drive_strength_opt delay3_opt gate_instance_brace ';'
		{ init($$, ID_inst_builtin); addswap($$, ID_module, $1); swapop($$, $4); }
	| n_output_gatetype drive_strength_opt delay3_opt gate_instance_brace ';'
		{ init($$, ID_inst_builtin); addswap($$, ID_module, $1); swapop($$, $4); }
	| pass_en_switchtype delay3_opt gate_instance_brace ';'
		{ init($$, ID_inst_builtin); addswap($$, ID_module, $1); swapop($$, $3); }
	| pass_switchtype gate_instance_brace ';'
		{ init($$, ID_inst_builtin); addswap($$, ID_module, $1); swapop($$, $2); }
	| TOK_PULLDOWN pulldown_strength_opt gate_instance_brace ';'
		{ init($$, ID_inst_builtin); stack_expr($$).set(ID_module, ID_pulldown); swapop($$, $3); }
	| TOK_PULLUP   pullup_strength_opt   gate_instance_brace ';'
		{ init($$, ID_inst_builtin); stack_expr($$).set(ID_module, ID_pullup);   swapop($$, $3); }
	;

// System Verilog standard 1800-2017
// A.3.2 Primitive strengths

pulldown_strength_opt:
	  /* Optional */ { make_nil($$); }
//	| pulldown_strength
	;

/*
pulldown_strength:
	  '(' strength0 ',' strength1 ')'
	| '(' strength1 ',' strength0 ')'
	| '(' strength0 ')'
	;
*/

pullup_strength_opt:
	  /* Optional */ { make_nil($$); }
//	| pullup_strength
	;

/*
pullup_strength:
	  '(' strength0 ',' strength1 ')'
	| '(' strength1 ',' strength0 ')'
	| '(' strength1 ')'
	;
*/

// System Verilog standard 1800-2017
// A.3.4 Primitive gate and switch types

cmos_switchtype:
	  TOK_CMOS     { init($$, ID_cmos); }
	| TOK_RCMOS    { init($$, ID_rcmos); }
	;

enable_gatetype:
	  TOK_BUFIF0   { init($$, ID_bufif0); }
	| TOK_BUFIF1   { init($$, ID_bufif1); }
	| TOK_NOTIF0   { init($$, ID_notif0); }
	| TOK_NOTIF1   { init($$, ID_notif1); }
	;

mos_switchtype:
	  TOK_NMOS     { init($$, ID_nmos); }
	| TOK_PMOS     { init($$, ID_pmos); }
	| TOK_RNMOS    { init($$, ID_rnmos); }
	| TOK_RPMOS    { init($$, ID_rpmos); }
	;

n_input_gatetype:
	  TOK_AND      { init($$, ID_and); }
	| TOK_NAND     { init($$, ID_nand); }
        | TOK_NOR      { init($$, ID_nor); }
        | TOK_OR       { init($$, ID_or); }
	| TOK_XNOR     { init($$, ID_nor); }
        | TOK_XOR      { init($$, ID_xor); }
	;

n_output_gatetype:
	  TOK_BUF      { init($$, ID_buf); }
	| TOK_NOT      { init($$, ID_not); }
	;

pass_en_switchtype:
	  TOK_RTRAN    { init($$, "rtran"); }
	| TOK_RTRANIF0 { init($$, "rtranif0"); }
	| TOK_RTRANIF1 { init($$, "rtranif0"); }
	| TOK_TRAN     { init($$, "rtranif1"); }
	;

pass_switchtype:
 	  TOK_TRANIF0  { init($$, "tranif0"); }
	| TOK_TRANIF1  { init($$, "tranif1"); }
	;

gate_instance_brace:
	  gate_instance
		{ init($$); mto($$, $1); }
	| gate_instance_brace ',' module_instance
		{ $$=$1;    mto($$, $3); }
	;

gate_instance:
	  name_of_gate_instance_opt range_opt '(' list_of_module_connections_opt ')'
		{ init($$, ID_inst); addswap($$, ID_instance, $1);
                  swapop($$, $4);
                  addswap($$, ID_range, $2);
                }
	;

name_of_gate_instance_opt:
	  /* Optional */ 
	        { init($$, "$_&#ANON" + PARSER.get_dummy_id()); }
	| name_of_gate_instance
	;

name_of_gate_instance: TOK_CHARSTR;

// System Verilog standard 1800-2017
// A.4.1.1 Module instantiation

module_instantiation:
	  module_identifier param_value_assign_opt module_instance_brace ';'
		{ init($$, ID_inst);
                  addswap($$, ID_module, $1);
		  addswap($$, ID_parameter_assignments, $2);
                  swapop($$, $3); }
	;

param_value_assign_opt:
	  /* Optional */
		{ make_nil($$); }
	| '#' '(' list_of_parameter_assignments ')'
		{ $$ = $3; }
	;

list_of_parameter_assignments:
	  ordered_parameter_assignment_brace
	| named_parameter_assignment_brace
	;

ordered_parameter_assignment_brace:
	  ordered_parameter_assignment
	  	{ init($$); mto($$, $1); }
	| ordered_parameter_assignment_brace ',' ordered_parameter_assignment
	  	{ $$=$1; mto($$, $3); }
	;

named_parameter_assignment_brace:
	  named_parameter_assignment
	  	{ init($$); mto($$, $1); }
	| named_parameter_assignment_brace ',' named_parameter_assignment
	  	{ $$=$1; mto($$, $3); }
	;

ordered_parameter_assignment:
          expression;

named_parameter_assignment:
	  '.' parameter_identifier '(' expression_opt ')'
	  	{ init($$, ID_named_parameter_assignment);
	  	  stack_expr($$).add(ID_parameter).swap(stack_expr($2));
	  	  stack_expr($$).add(ID_value).swap(stack_expr($4));
	  	}
	;

module_instance_brace:
	  module_instance
		{ init($$); mto($$, $1); }
	| module_instance_brace ',' module_instance
		{ $$=$1;    mto($$, $3); }
	;

module_instance:
	  name_of_instance '(' list_of_module_connections_opt ')'
		{ init($$, ID_inst); addswap($$, ID_instance, $1); swapop($$, $3); }
	;

name_of_instance: { init($$, "$_&#ANON" + PARSER.get_dummy_id());}
| 
TOK_CHARSTR;

list_of_module_connections_opt:
		/* Optional */
		/* { make_nil($$); }
	| */ list_of_module_connections
	;

list_of_module_connections:
	  ordered_port_connection_brace
	| named_port_connection_brace
	;

ordered_port_connection_brace:
	  ordered_port_connection
		{ init($$); mto($$, $1); }
	| ordered_port_connection_brace ',' ordered_port_connection
		{ $$=$1;    mto($$, $3); }
	;

ordered_port_connection:
	  expression_opt
	;

named_port_connection_brace:
	  named_port_connection
		{ init($$); mto($$, $1); }
	| named_port_connection_brace ',' named_port_connection
		{ $$=$1;    mto($$, $3); }
	;

named_port_connection:
	  '.' port_identifier '(' expression_opt ')'
		{ init($$, ID_named_port_connection);
                  mto($$, $2);
                  mto($$, $4); }
	;

// System Verilog standard 1800-2017
// A.4.2 Generated instantiation

generate_region:
	  TOK_GENERATE generate_item_brace TOK_ENDGENERATE
		{ init($$, ID_generate_block); swapop($$, $2); }
	;

generate_item_brace:
	  /* Optional */
		{ init($$); }
	| generate_item_brace generate_item
		{ $$=$1; mto($$, $2); }
	;

loop_generate_construct:
	  // The following is a generalisation of the Verilog 2001
	  // grammar, which requires begin ... end, and does not allow
	  // the generate_item. Found in the SystemVerilog IEEE 1800-2012
	  // grammar.
	  TOK_FOR '(' genvar_initialization ';'
	              constant_expression ';'
                      genvar_initialization ')'
          // generate_block
          generate_item
		{ init($$, ID_generate_for);
		  stack_expr($$).reserve_operands(4);
		  mto($$, $3);
		  mto($$, $5);
		  mto($$, $7);
		  mto($$, $9);
		}
        ;

genvar_initialization:
	  genvar_identifier '=' constant_expression
	  	{ init($$, ID_generate_assign); mto($$, $1); mto($$, $3); }
	;

conditional_generate_construct:
	  if_generate_construct
	| case_generate_construct
	;

if_generate_construct:
	  TOK_IF '(' constant_expression ')' generate_item_or_null %prec LT_TOK_ELSE
	  	{ init($$, ID_generate_if); mto($$, $3); mto($$, $5); }
	| TOK_IF '(' constant_expression ')' generate_item_or_null TOK_ELSE generate_item_or_null
	  	{ init($$, ID_generate_if); mto($$, $3); mto($$, $5); mto($$, $7); }
	;

case_generate_construct:
	  TOK_CASE '(' constant_expression ')'
	  case_generate_item_brace TOK_ENDCASE
	  	{ init($$, ID_generate_case); mto($$, $3); }
	;

case_generate_item_brace:
	  case_generate_item
	| case_generate_item_brace case_generate_item
	;

case_generate_item:
	  expression_brace TOK_COLON generate_item_or_null
	| TOK_DEFAULT TOK_COLON generate_item_or_null
	| TOK_DEFAULT generate_item_or_null
	;

generate_block:
	  TOK_BEGIN generate_item_brace TOK_END
		{ init($$, ID_generate_block); swapop($$, $2); }
	| TOK_BEGIN TOK_COLON generate_block_identifier generate_item_brace TOK_END
		{ init($$, ID_generate_block);
		  swapop($$, $4);
		  stack_expr($$).set(ID_identifier, stack_expr($3).id()); }
	;

generate_item:
	  conditional_generate_construct
	| loop_generate_construct
	| generate_block
	| module_or_generate_item
	;

generate_item_or_null:
	  generate_item
	| ';' { init($$, ID_generate_skip); }
	;

constant_expression: expression;

package_or_generate_item_declaration:
	  net_declaration
	| data_declaration
	| task_declaration
	| function_declaration
	| local_parameter_declaration ';'
	| parameter_declaration ';'
        ;
	
// System Verilog standard 1800-2017
// A.5.1 UDP declaration

udp_declaration: attribute_instance_brace TOK_PRIMITIVE udp_identifier 
	  '(' udp_port_list ')' ';' udp_port_declaration_brace
	  udp_body TOK_ENDPRIMITIVE
	| attribute_instance_brace TOK_PRIMITIVE udp_identifier 
	  '(' udp_declaration_port_list ')' ';'
	  udp_body TOK_ENDPRIMITIVE
	;

// System Verilog standard 1800-2017
// A.5.2 UDP ports

udp_port_list: port_identifier ',' port_identifier_brace
	;

udp_port_declaration_brace:
	  udp_port_declaration
	| udp_port_declaration_brace udp_port_declaration
	;

udp_port_declaration:
	  udp_output_declaration ';'
	| udp_input_declaration  ';'
	| udp_reg_declaration    ';'
	;

udp_output_declaration:
	  attribute_instance_brace TOK_OUTPUT port_identifier
	;

udp_input_declaration:
	  attribute_instance_brace TOK_INPUT list_of_port_identifiers
	;

udp_reg_declaration:
	  attribute_instance_brace TOK_REG variable_identifier
	;

udp_declaration_port_list: udp_output_declaration ',' udp_input_declaration_brace
	;

udp_input_declaration_brace:
	  udp_input_declaration
	| udp_input_declaration_brace udp_input_declaration
	;

port_identifier_brace:
	  port_identifier
	| port_identifier_brace ',' port_identifier
	;

// System Verilog standard 1800-2017
// A.5.3 UDP body

udp_body: udp_initial_statement_opt TOK_TABLE table_entry_brace TOK_ENDTABLE
	;

udp_initial_statement_opt:
	;

table_entry_brace:
	  table_entry
	| table_entry_brace table_entry
	;

table_entry: input_list TOK_COLON output_or_level_symbol ';'
	| input_list TOK_COLON output_or_level_symbol TOK_COLON next_state ';'
	;

input_list:;

output_or_level_symbol:;

next_state:;

list_of_port_declarations: '(' port_declaration_brace ')' { $$=$2; }
	;

list_of_ports_opt:
	/* Optional */
              { make_nil($$); }
	| list_of_ports
	;

// System Verilog standard 1800-2017
// A.6.1 Continuous assignment and net alias statements

continuous_assign:
	  TOK_ASSIGN delay3_opt list_of_net_assignments ';'
		{ init($$, ID_continuous_assign); swapop($$, $3); }
	;

list_of_net_assignments:
	  net_assignment
		{ init($$); mto($$, $1); }
	| list_of_net_assignments ',' net_assignment
		{ $$=$1;    mto($$, $3); }
	;

net_assignment: net_lvalue '=' expression
		{ init($$, ID_equal); mto($$, $1); mto($$, $3); }
	;

variable_assignment: net_assignment;

// System Verilog standard 1800-2017
// A.6.2 Procedural blocks and assignments

initial_construct: TOK_INITIAL statement
		{ init($$, ID_initial); mto($$, $2); }
	;

always_construct: TOK_ALWAYS statement
		{ init($$, ID_always); mto($$, $2); }
	;

// The extra rule to allow block_item_declaration is to avoid an ambiguity
// caused by the attribute_instance_brace.
statement: 
/*          block_identifier TOK_COLON attribute_instance_brace statement_item
                { $$=$4; }
        | */ 
          attribute_instance_brace statement_item
                { $$=$2; }
        | block_item_declaration
        ;

statement_item:
          assert_property_statement
        | assume_property_statement
        | blocking_assignment ';' { $$ = $1; }
	| nonblocking_assignment ';' { $$ = $1; }
	| case_statement
	| cover_property_statement
	| conditional_statement
	| inc_or_dec_expression ';'
	| subroutine_call_statement
	| disable_statement
	| event_trigger
	| loop_statement
	| par_block
	| procedural_timing_control_statement
	| procedural_continuous_assignments ';'
	| seq_block
	| wait_statement
	| immediate_assert_statement
	;

subroutine_call_statement:
          subroutine_call ';'
                { $$=$1; }
        ;

subroutine_call:
          tf_call
        | system_tf_call
        ;
        
// System Verilog standard 1800-2017
// A.6.3 Parallel and sequential blocks

action_block:
          statement_or_null %prec LT_TOK_ELSE
        | statement_or_null TOK_ELSE statement 
                { init($$, "action-else"); stack_expr($$).operands().resize(2);
                  to_binary_expr(stack_expr($$)).op0().swap(stack_expr($0));
                  to_binary_expr(stack_expr($$)).op1().swap(stack_expr($2)); }
	;

concurrent_assert_statement:
          assert_property_statement
        | block_identifier TOK_COLON assert_property_statement
		{ 
		  $$=$3;
		  stack_expr($$).set(ID_identifier, stack_expr($1).id());
		}
	;

concurrent_assume_statement:
          assume_property_statement
        | block_identifier TOK_COLON assume_property_statement
		{ 
		  $$=$3;
		  stack_expr($$).set(ID_identifier, stack_expr($1).id());
		}
	;

concurrent_cover_statement: cover_property_statement
        | block_identifier TOK_COLON cover_property_statement
		{ 
		  $$=$3;
		  stack_expr($$).set(ID_identifier, stack_expr($1).id());
		}
	;

// System Verilog standard 1800-2017
// A.6.4 Statements

statement_or_null_brace:
		/* Optional */
		{ init($$); }
	| statement_or_null_brace statement_or_null
		{ $$=$1; mto($$, $2); }
	;

system_task_name: TOK_SYSIDENT
                { init($$, ID_symbol);
                  stack_expr($$).set(ID_identifier, stack_expr($1).id());
                }
        ;

// System Verilog standard 1800-2017
// A.6.5 Timing control statements

delay_or_event_control:
	  delay_control
	| event_control
	| TOK_REPEAT '(' expression ')' event_control
	        { init($$, ID_repeat); }
	;

delay_control:
	  '#' delay_value
		{ init($$, ID_delay); mto($$, $2); }
	| '#' '(' mintypmax_expression ')'
		{ init($$, ID_delay); mto($$, $2); }
	;

event_control:
	  '@' event_identifier
		{ init($$, ID_event_guard); mto($$, $2); }
	| '@' '(' ored_event_expression ')'
		{ init($$, ID_event_guard); mto($$, $3); }
	| '@' TOK_ASTERIC
		{ init($$, ID_event_guard);
		  stack_expr($$).operands().resize(1);
	          to_unary_expr(stack_expr($$)).op().id(ID_verilog_star_event); }
	| '@' '(' TOK_ASTERIC ')'
		{ init($$, ID_event_guard);
		  stack_expr($$).operands().resize(1);
	          to_unary_expr(stack_expr($$)).op().id(ID_verilog_star_event); }
	| '@' TOK_PARENASTERIC ')'
		{ init($$, ID_event_guard);
		  stack_expr($$).operands().resize(1);
	          to_unary_expr(stack_expr($$)).op().id(ID_verilog_star_event); }
	;

ored_event_expression:
	  event_expression
		{ init($$, ID_event); mto($$, $1); }
	| ored_event_expression TOK_OR event_expression
		{ $$=$1; mto($$, $3); }
	| ored_event_expression ',' event_expression
		{ $$=$1; mto($$, $3); }
	;

event_expression:
	  expression
		{ $$=$1; }
	| TOK_POSEDGE expression
		{ init($$, ID_posedge); mto($$, $2); }
	| TOK_NEGEDGE expression
		{ init($$, ID_negedge); mto($$, $2); }
	;

// System Verilog standard 1800-2017
// A.6.6 Conditional statements

conditional_statement:
	  TOK_IF '(' expression ')' statement_or_null %prec LT_TOK_ELSE
		{ init($$, ID_if); mto($$, $3); mto($$, $5); }
	| TOK_IF '(' expression ')' statement_or_null TOK_ELSE statement_or_null
		{ init($$, ID_if); mto($$, $3); mto($$, $5); mto($$, $7); }
	;

// System Verilog standard 1800-2017
// A.6.7 Case statements

case_statement:
	  TOK_CASE '(' expression ')' case_item_brace TOK_ENDCASE
		{ init($$, ID_case);  mto($$, $3);
                  Forall_operands(it, stack_expr($5))
                    stack_expr($$).add_to_operands(std::move(*it)); }
	| TOK_CASEX '(' expression ')' case_item_brace TOK_ENDCASE
		{ init($$, ID_casex); mto($$, $3);
                  Forall_operands(it, stack_expr($5))
                    stack_expr($$).add_to_operands(std::move(*it)); }
	| TOK_CASEZ '(' expression ')' case_item_brace TOK_ENDCASE
		{ init($$, ID_casez); mto($$, $3);
                  Forall_operands(it, stack_expr($5))
                    stack_expr($$).add_to_operands(std::move(*it)); }
	;

case_item_brace:
	  case_item
		{ init($$); mto($$, $1); }
	| case_item_brace case_item
		{ $$=$1; mto($$, $2); }
	;

case_item:
	  expression_brace TOK_COLON statement_or_null
		{ init($$, ID_case_item); mto($$, $1); mto($$, $3); }
	| TOK_DEFAULT TOK_COLON statement_or_null
		{ init($$, ID_case_item);
                  stack_expr($$).operands().resize(1);
                  to_unary_expr(stack_expr($$)).op().id(ID_default);
                  mto($$, $3); }
	| TOK_DEFAULT statement_or_null
		{ init($$, ID_case_item);
                  stack_expr($$).operands().resize(1);
                  to_unary_expr(stack_expr($$)).op().id(ID_default);
                  mto($$, $2); }
	;

// System Verilog standard 1800-2017
// A.6.8 Looping statements

loop_statement:
	  TOK_FOREVER statement
		{ init($$, ID_forever); mto($$, $2); }
	| TOK_REPEAT '(' expression ')' statement
		{ init($$, ID_repeat); mto($$, $3); mto($$, $5); }
	| TOK_WHILE '(' expression ')' statement
		{ init($$, ID_while); mto($$, $3); mto($$, $5); }
	| TOK_FOR '(' for_initialization ';' expression ';' for_step ')' statement
		{ init($$, ID_for); mto($$, $3); mto($$, $5); mto($$, $7); mto($$, $9); }
	;

for_initialization: blocking_assignment
        ;

for_step: for_step_assignment
        ;

for_step_assignment:
          operator_assignment
        | inc_or_dec_expression
        ;

// The 1800-2017 grammar contains a block_item_declartion_brace before
// the statement_or_null brace. This yields ambiguity owing to the
// attribute_inance_brace in block_item_declaration and in
// statement. Instead, we extend the statement rule to accept
// block_item_declaration.
seq_block:
	  TOK_BEGIN
	  statement_or_null_brace
	  TOK_END
		{ init($$, ID_block); swapop($$, $2); }
        | TOK_BEGIN TOK_COLON block_identifier
          statement_or_null_brace
          TOK_END
                { init($$, ID_block);
                  swapop($$, $4);
                  addswap($$, ID_identifier, $3); }
	;

block_item_declaration_brace:
	  /* Optional */
		{ init($$); }
	| block_item_declaration_brace block_item_declaration
		{ $$=$1; mto($$, $2); }
	;

statement_brace:
		/* Optional */
		{ init($$); }
	| statement_brace statement
		{ $$=$1; mto($$, $2); }
	;

// System Verilog standard 1800-2017
// A.6.10 Assertion statements

immediate_assert_statement: TOK_ASSERT '(' expression ')' action_block
		{ init($$, ID_assert); mto($$, $3); mto($$, $5); }
	;

wait_statement: TOK_WAIT '(' expression ')' statement_or_null
		{ init($$, ID_wait); mto($$, $3); mto($$, $5); }
	;

procedural_continuous_assignments:
	  TOK_ASSIGN variable_assignment
		{ init($$, ID_continuous_assign); mto($$, $2); }
	| TOK_DEASSIGN variable_lvalue
		{ init($$, ID_deassign); mto($$, $2); }
	| TOK_FORCE variable_assignment
		{ init($$, ID_force); swapop($$, $2); }
	/* | TOK_FORCE net_assignment */
	| TOK_RELEASE variable_lvalue
		{ init($$, ID_release); mto($$, $2); }
	/* | TOK_RELEASE net_lvalue */
	;

blocking_assignment:
	  variable_lvalue '=' delay_or_event_control expression
		{ init($$, ID_blocking_assign); mto($$, $1); mto($$, $4); }
        | operator_assignment
	;
	
operator_assignment:
          variable_lvalue assignment_operator expression
		{ init($$, ID_blocking_assign); mto($$, $1); mto($$, $3); }
        ;

assignment_operator:
          '='
        | TOK_PLUSEQUAL
        | TOK_MINUSEQUAL
        | TOK_ASTERICEQUAL
        | TOK_SLASHEQUAL
        | TOK_PERCENTEQUAL
        | TOK_AMPEREQUAL
        | TOK_VERTBAREQUAL
        | TOK_CARETEQUAL
        | TOK_LESSLESSEQUAL
        | TOK_GREATERGREATEREQUAL
        | TOK_LESSLESSLESSEQUAL
        | TOK_GREATERGREATERGREATEREQUAL
        ;

nonblocking_assignment:
	  variable_lvalue TOK_LESSEQUAL expression
		{ init($$, ID_non_blocking_assign); mto($$, $1); mto($$, $3); }
	| variable_lvalue TOK_LESSEQUAL delay_or_event_control expression
		{ init($$, ID_non_blocking_assign); mto($$, $1); mto($$, $4); }
	;

procedural_timing_control_statement:
          procedural_timing_control statement_or_null
		{ $$=$1; mto($$, $2); }
	;

procedural_timing_control:
          delay_control
        | event_control
        | cycle_delay
        ;

// System Verilog standard 1800-2017
// A.6.11 Clocking block

cycle_delay:
          "##" number
                { init($$, ID_verilog_cycle_delay); mto($$, $2); }
        | "##" identifier
                { init($$, ID_verilog_cycle_delay); mto($$, $2); }
        | "##" '(' expression ')'
                { init($$, ID_verilog_cycle_delay); mto($$, $3); }
        ;

// System Verilog standard 1800-2017
// A.7.1 Specify block declaration

specify_block: TOK_SPECIFY specify_item_brace TOK_ENDSPECIFY
		{ init($$, ID_specify); } 
	;

specify_item_brace:
	  /* Optional */
	| specify_item_brace specify_item
	;

specify_item: specparam_declaration
      //              | pulsestyle_declaration
      //              | showcancelled_declaration
      //  path_declaration
	  system_timing_check
        ;

// System Verilog standard 1800-2017
// A.7.2 Specify path declarations

path_declaration:
	  simple_path_declaration ';'
	| state_dependent_path_declaration ';'
  //    | edge_sensitive_path_declaration ';'
	;

simple_path_declaration:
	  full_path_description '=' '(' path_delay_value ')'
	| parallel_path_description '=' '(' list_path_delay_value ')'
	;
	
list_path_delay_value:
	;

state_dependent_path_declaration:
	  TOK_IF '(' expression ')' simple_path_declaration
	| TOK_IFNONE simple_path_declaration
	;

parallel_path_description:
	  '(' specify_input_terminal_descriptor
	  '[' polarity_operator ']' '=' TOK_GREATER
	  specify_output_terminal_descriptor ')'
	;

full_path_description: 
	  '(' port_brace polarity_operator TOK_ASTERIC
	  TOK_GREATER port_brace ')'
	;

// System Verilog standard 1800-2017
// A.7.4 Specify path delays

path_delay_value:
          mintypmax_expression
	| path_delay_value ',' mintypmax_expression
	;

specify_input_terminal_descriptor: port_identifier range_opt;
specify_output_terminal_descriptor: port_identifier range_opt;

polarity_operator: 
          /* nothing */
	| TOK_PLUS
	| TOK_MINUS
	;

list_of_specparam_assignments: 
	  specparam_assignment 
	| list_of_specparam_assignments ',' specparam_assignment
	;

specparam_assignment:
	  specparam_identifier '=' mintypmax_expression
	;

system_timing_check: timing_3 ';'
	;

timing_3: 
          timing_type '(' event_expression ',' 
          event_expression ',' expression ',' variable_identifier ')'
        ;

timing_type:
	  TOK_SETUP
	| TOK_HOLD
	| TOK_RECOVERY
	| TOK_REMOVAL
	| TOK_SKEW
	| TOK_WIDTH
	;

// System Verilog standard 1800-2017
// A.8.1 Concatenations

concatenation: '{' expression_brace '}'
		{ init($$, ID_concatenation); swapop($$, $2); }
	;

replication:
          '{' expression concatenation '}'
		{ init($$, ID_replication); mto($$, $2); mto($$, $3); }
        | '{' expression replication '}'
		{ init($$, ID_replication); mto($$, $2); mto($$, $3); }
	;

function_subroutine_call: subroutine_call
        ;

expression_brace_opt:
	  /* Optional */
          { make_nil($$); }
	| '(' expression_brace ')'
		{ $$ = $2; }
	;

unsigned_number: TOK_NUMBER
        ;

// System Verilog standard 1800-2017
// A.8.2 Subroutine calls

tf_call:
          hierarchical_tf_identifier '(' expression_brace ')'
		{ init($$, ID_function_call);
		  stack_expr($$).operands().reserve(2);
		  mto($$, $1); mto($$, $3); }
        ;

system_tf_call:
	  system_task_name
		{ init($$, ID_function_call);
		  stack_expr($$).operands().resize(2);
		  stack_expr($$).operands()[0].swap(stack_expr($1)); }
        | system_task_name '(' expression_brace ')'
		{ init($$, ID_function_call);
		  stack_expr($$).operands().reserve(2);
		  mto($$, $1); mto($$, $3); }
        ;


statement_or_null:
	  statement
	| attribute_instance_brace ';' { init($$, ID_skip); }
	;

event_trigger: TOK_MINUSGREATER hierarchical_event_identifier ';'
	;

par_block:
	  TOK_FORK statement_or_null_brace TOK_JOIN
		{ init($$, ID_fork); swapop($$, $2); }
        | TOK_FORK TOK_COLON block_identifier
          statement_or_null_brace TOK_JOIN
                { init($$, ID_block);
                  swapop($$, $4);
                  addswap($$, ID_identifier, $3); }

	;

disable_statement: TOK_DISABLE hierarchical_task_or_block_identifier ';'
		{ init($$, ID_disable); mto($$, $2); }
	;

// System Verilog standard 1800-2017
// A.8.3 Expressions

inc_or_dec_expression:
          TOK_PLUSPLUS attribute_instance_brace variable_lvalue
                { init($$, ID_preincrement); mto($$, $3); }
        | TOK_MINUSMINUS attribute_instance_brace variable_lvalue
                { init($$, ID_predecrement); mto($$, $3); }
        | variable_lvalue attribute_instance_brace TOK_PLUSPLUS
                { init($$, ID_postincrement); mto($$, $1); }
        | variable_lvalue attribute_instance_brace TOK_MINUSMINUS
                { init($$, ID_postdecrement); mto($$, $1); }
        ;

// System Verilog standard 1800-2017
// A.8.4 Primaries

primary:  primary_literal
        | indexed_variable_lvalue
	| indexed_variable_lvalue part_select
		{ extractbits($$, $1, $2); }
	| indexed_variable_lvalue indexed_part_select
		{ extractbits($$, $1, $2); }
	| concatenation 
        | replication
        | function_subroutine_call
	| '(' mintypmax_expression ')'
		{ $$ = $2; }
        | TOK_NULL { init($$, ID_NULL); }
	;

primary_literal:
          number
        | time_literal
        ;

time_literal: TOK_TIME_LITERAL
		{ init($$, ID_constant);
		  addswap($$, ID_value, $1);
		  stack_expr($$).type().id(ID_verilog_realtime); }
	;

// System Verilog standard 1800-2017
// A.8.5 Expression left-side values

net_lvalue: variable_lvalue;

variable_lvalue:
	  indexed_variable_lvalue
	| indexed_variable_lvalue part_select
		{ extractbits($$, $1, $2); }
	| indexed_variable_lvalue indexed_part_select
		{ extractbits($$, $1, $2); }
        | concatenation
          /* more generous than the rule below to avoid conflict */
        /*
        | '{' variable_concatenation_lvalue_brace '}'
		{ init($$, ID_concatenation); swapop($$, $2); }
        */
	;
	
variable_concatenation_lvalue_brace:
	  variable_lvalue
		{ init($$); mto($$, $1); }
	| variable_concatenation_lvalue_brace ',' variable_lvalue
		{ $$=$1;    mto($$, $3); }
	;

indexed_variable_lvalue:
	  hierarchical_variable_identifier
	| indexed_variable_lvalue bit_select
		{ extractbit($$, $1, $2); }
	;
	
const_expression: expression;

mintypmax_expression:
	  expression
	| expression TOK_COLON expression TOK_COLON expression
		{ init($$, "mintypmax"); mto($$, $1); mto($$, $3); mto($$, $5); }
	;

expression_opt:
	  /* Optional */
	  { make_nil($$); }
	| expression
	;

expression_brace:
	  expression
		{ init($$); mto($$, $1); }
	| expression_brace ',' expression
		{ $$=$1;    mto($$, $3); }
	;

expression:
          primary
        | unary_operator attribute_instance_brace primary
                { $$=$1; mto($$, $3); }
        | inc_or_dec_expression
	| expression TOK_PLUS expression
		{ init($$, ID_plus); mto($$, $1); mto($$, $3); }
	| expression TOK_MINUS expression
		{ init($$, ID_minus); mto($$, $1); mto($$, $3); }
	| TOK_PLUS expression %prec UNARY_PLUS
		{ init($$, ID_unary_plus); mto($$, $2); }
	| TOK_MINUS expression %prec UNARY_MINUS
		{ init($$, ID_unary_minus); mto($$, $2); }
	| expression TOK_ASTERIC expression
		{ init($$, ID_mult); mto($$, $1); mto($$, $3); }
	| expression TOK_SLASH expression
		{ init($$, ID_div); mto($$, $1); mto($$, $3); }
	| expression TOK_PERCENT expression
		{ init($$, ID_mod); mto($$, $1); mto($$, $3); }
	| expression TOK_EQUALEQUAL expression
		{ init($$, ID_equal); mto($$, $1); mto($$, $3); }
	| expression TOK_EXCLAMEQUAL expression
		{ init($$, ID_notequal); mto($$, $1); mto($$, $3); }
	| expression TOK_EQUALEQUALEQUAL expression
		{ init($$, ID_verilog_case_equality); mto($$, $1); mto($$, $3); }
	| expression TOK_EXCLAMEQUALEQUAL expression
		{ init($$, ID_verilog_case_inequality); mto($$, $1); mto($$, $3); }
	| expression TOK_AMPERAMPER expression
		{ init($$, ID_and); mto($$, $1); mto($$, $3); }
	| expression TOK_ASTERICASTERIC expression
		{ init($$, ID_power); mto($$, $1); mto($$, $3); }
	| expression TOK_VERTBARVERTBAR expression
		{ init($$, ID_or); mto($$, $1); mto($$, $3); }
	| expression TOK_LESS expression
		{ init($$, ID_lt); mto($$, $1); mto($$, $3); }
	| expression TOK_LESSEQUAL expression
		{ init($$, ID_le); mto($$, $1); mto($$, $3); }
	| expression TOK_GREATER expression
		{ init($$, ID_gt); mto($$, $1); mto($$, $3); }
	| expression TOK_GREATEREQUAL expression
		{ init($$, ID_ge); mto($$, $1); mto($$, $3); }
	| expression TOK_AMPER expression
		{ init($$, ID_bitand); mto($$, $1); mto($$, $3); }
	| expression TOK_VERTBAR expression
		{ init($$, ID_bitor); mto($$, $1); mto($$, $3); }
	| expression TOK_CARET expression
		{ init($$, ID_bitxor); mto($$, $1); mto($$, $3); }
	| expression TOK_TILDECARET expression
		{ init($$, ID_bitxnor); mto($$, $1); mto($$, $3); }
	| expression TOK_LESSLESS expression
		{ init($$, ID_shl); mto($$, $1); mto($$, $3); }
	| expression TOK_LESSLESSLESS expression
		{ init($$, ID_shl); mto($$, $1); mto($$, $3); }
	| expression TOK_GREATERGREATER expression
		{ init($$, ID_lshr); mto($$, $1); mto($$, $3); }
	| expression TOK_GREATERGREATERGREATER expression
	        // This is an arithmetic right shift for signed expressions,
	        // and a logical right shift otherwise -- the type checker
	        // will determine.
		{ init($$, ID_shr); mto($$, $1); mto($$, $3); }
	| expression TOK_QUESTION expression TOK_COLON expression
		{ init($$, ID_if); mto($$, $1); mto($$, $3); mto($$, $5); }
	| TOK_QSTRING
		{ init($$, ID_constant); stack_expr($$).type()=typet(ID_string); addswap($$, ID_value, $1); }
	;

// System Verilog standard 1800-2017
// A.8.6 Operators

unary_operator:
	  TOK_TILDE        { init($$, ID_bitnot); }
	| TOK_EXCLAM       { init($$, ID_not); }
	| TOK_AMPER        { init($$, ID_reduction_and); }
	| TOK_TILDEAMPER   { init($$, ID_reduction_nand); }
	| TOK_VERTBAR      { init($$, ID_reduction_or); }
	| TOK_TILDEVERTBAR { init($$, ID_reduction_nor); }
	| TOK_CARET        { init($$, ID_reduction_xor); }
	| TOK_CARETTILDE   { init($$, ID_reduction_xnor); }
	| TOK_TILDECARET   { init($$, ID_reduction_xnor); }
        ;

// System Verilog standard 1800-2017
// A.8.7 Numbers

number: unsigned_number
		{ init($$, ID_constant); addswap($$, ID_value, $1); }
	;

// System Verilog standard 1800-2017
// A.9.1 Attributes

attribute_instance_brace:
	  /* Optional */
		{ init($$, ID_verilog_attribute); }
	| attribute_instance_brace attribute_instance
		{ $$=$1;
		  for(auto &attr : stack_expr($2).get_sub())
		    stack_expr($$).move_to_sub(attr);
		}
        ;

attribute_instance: TOK_PARENASTERIC attr_spec_list TOK_ASTERICPAREN
		{ $$=$2; }
        ;

attr_spec_list:
	  attr_spec
	  	{ init($$); }
	| attr_spec_list ',' attr_spec
		{ $$=$1; mts($$, $3); }
        ;

attr_spec: attr_name '=' constant_expression
		{ init($$, "attribute");
		  stack_expr($$).add(ID_name).swap(stack_expr($1));
		  stack_expr($$).add(ID_value).swap(stack_expr($3));
		}
	| attr_name
		{ init($$, "attribute"); stack_expr($$).add(ID_name).swap(stack_expr($1)); }
	;

attr_name: identifier
	;

// System Verilog standard 1800-2017
// A.9.3 Identifiers

block_identifier: TOK_CHARSTR;

genvar_identifier: TOK_CHARSTR
		{ new_symbol($$, $1); }
	;

hierarchical_parameter_identifier: hierarchical_identifier
	;

interface_identifier:
	;

module_identifier: TOK_CHARSTR;

module_identifier_opt:
	  /* Optional */
	| module_identifier
	;

net_identifier: TOK_CHARSTR
		{ new_symbol($$, $1); }
	;

param_identifier: TOK_CHARSTR;

port_identifier: TOK_CHARSTR
		{ new_symbol($$, $1); }
	;

ps_covergroup_identifier:
	;
	
memory_identifier: TOK_CHARSTR
		{ new_symbol($$, $1); }
	;

type_identifier: TOK_CHARSTR
		{ new_symbol($$, $1); }
	;

parameter_identifier: TOK_CHARSTR;

generate_block_identifier: TOK_CHARSTR;

udp_identifier: TOK_CHARSTR;

task_identifier: hierarchical_identifier
	;

event_identifier:
          TOK_CHARSTR
		{ new_symbol($$, $1); }
        ;

hierarchical_task_or_block_identifier: task_identifier;

hierarchical_tf_identifier: hierarchical_identifier;

specparam_identifier: TOK_CHARSTR; 

function_identifier: hierarchical_identifier
	;

hierarchical_event_identifier: event_identifier;

hierarchical_identifier:
          identifier
        | hierarchical_identifier '.' identifier
		{ init($$, ID_hierarchical_identifier);
		  stack_expr($$).reserve_operands(2);
		  mto($$, $1);
		  mto($$, $3);
		}
	;
	
hierarchical_variable_identifier: hierarchical_identifier;

identifier: TOK_CHARSTR
		{ new_symbol($$, $1); }
	;

property_identifier: TOK_CHARSTR;

variable_identifier: TOK_CHARSTR
		{ new_symbol($$, $1); }
	;

%%
