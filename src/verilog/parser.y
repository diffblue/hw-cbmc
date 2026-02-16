/* increase verbosity of error messages, to include expected tokens */
%define parse.error verbose

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

#define PARSER (*verilog_parser_ptr)
#define YYSTYPE unsigned
#define YYSTYPE_IS_TRIVIAL 1

//#define YYDEBUG 1

#define mto(x, y) stack_expr(x).add_to_operands(std::move(stack_expr(y)))
#define mto2(x, y, z) stack_expr(x).add_to_operands(std::move(stack_expr(y)), std::move(stack_expr(z)))
#define mts(x, y) stack_expr(x).move_to_sub((irept &)stack_expr(y))
#define swapop(x, y) stack_expr(x).operands().swap(stack_expr(y).operands())
#define addswap(x, y, z) stack_expr(x).add(y).swap(stack_expr(z))
#define push_scope(base_name, separator, kind) PARSER.scopes.push_scope(base_name, separator, kind)
#define pop_scope() PARSER.scopes.pop_scope();

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

Function: new_identifier

  Inputs:

 Outputs:

 Purpose:


\*******************************************************************/

inline static void new_identifier(YYSTYPE &dest, YYSTYPE &src)
{
  init(dest, ID_verilog_identifier);
  const auto base_name = stack_expr(src).id();
  stack_expr(dest).set(ID_base_name, base_name);
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

Function: add_attributes

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static void add_attributes(YYSTYPE &dest, YYSTYPE &attributes)
{
  PRECONDITION(stack_expr(attributes).id() == ID_verilog_attributes);
  if(!stack_expr(attributes).get_sub().empty())
    addswap(dest, ID_verilog_attributes, attributes);
}

/*******************************************************************\

Function: yyverilogerror

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int yyverilogerror(const char *error)
{
  PARSER.parse_error(error, yyverilogtext);
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
%token TOK_LESSMINUSGREATER "<->"

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
%token TOK_INCDIR           "incdir"
%token TOK_INCLUDE          "include"
%token TOK_INITIAL          "initial"
%token TOK_INOUT            "inout"
%token TOK_INPUT            "input"
%token TOK_INSTANCE         "instance"
%token TOK_INTEGER          "integer"
%token TOK_JOIN             "join"
%token TOK_LARGE            "large"
%token TOK_LIBLIST          "liblist"
%token TOK_LIBRARY          "library"
%token TOK_LOCALPARAM       "localparam"
%token TOK_MACROMODULE      "macromodule"
%token TOK_MEDIUM           "medium"
%token TOK_MODULE           "module"
%token TOK_NAND             "nand"
%token TOK_NEGEDGE          "negedge"
%token TOK_NMOS             "nmos"
%token TOK_NOR              "nor"
%token TOK_NOSHOWCANCELLED  "noshowcancelled"
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
%token TOK_PULSESTYLE_ONDETECT "pulsestyle_ondetect"
%token TOK_PULSESTYLE_ONEVENT "pulsestyle_onevent"
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
%token TOK_USE              "use"
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
%token TOK_VERTBARMINUSGREATER  "|->"
%token TOK_VERTBAREQUALGREATER  "|=>"
%token TOK_PLUSPLUS             "++"
%token TOK_MINUSMINUS           "--"
%token TOK_PLUSEQUAL            "+="
%token TOK_PLUSCOLON            "+:"
%token TOK_MINUSEQUAL           "-="
%token TOK_MINUSCOLON           "-:"
%token TOK_ASTERICEQUAL         "*="
%token TOK_SLASHEQUAL           "/="
%token TOK_PERCENTEQUAL         "%="
%token TOK_AMPEREQUAL           "&="
%token TOK_CARETEQUAL           "^="
%token TOK_VERTBAREQUAL         "|="
%token TOK_LESSLESSEQUAL        "<<="
%token TOK_GREATERGREATEREQUAL  ">>="
%token TOK_LESSLESSLESSEQUAL    "<<<="
%token TOK_GREATERGREATERGREATEREQUAL ">>>="
%token TOK_HASHHASH             "##"
%token TOK_HASHMINUSHASH        "#-#"
%token TOK_HASHEQUALHASH        "#=#"
%token TOK_COLONCOLON           "::"
%token TOK_COLONEQUAL           ":="
%token TOK_COLONSLASH           ":/"
%token TOK_EQUALEQUALQUESTION   "==?"
%token TOK_EXCLAMEQUALQUESTION  "!=?"
%token TOK_LSQASTERIC           "[*"
%token TOK_LSQPLUS              "[+"
%token TOK_LSQEQUAL             "[="
%token TOK_LSQMINUSGREATER      "[->"
%token TOK_DOTASTERIC           ".*"

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
%token TOK_CELL             "cell"
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
%token TOK_DESIGN           "design"
%token TOK_DIST             "dist"
%token TOK_DO               "do"
%token TOK_ENDCHECKER       "endchecker"
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
%token TOK_FORKJOIN         "forkjoin"
%token TOK_GLOBAL           "global"
%token TOK_IFF              "iff"
%token TOK_IGNORE_BINS      "ignore_bins"
%token TOK_ILLEGAL_BINS     "illegal_bins"
%token TOK_IMPLEMENTS       "implements"
%token TOK_IMPLIES          "implies"
%token TOK_IMPORT           "import"
%token TOK_INSIDE           "inside"
%token TOK_INT              "int"
%token TOK_INTERCONNECT     "interconnect"
%token TOK_INTERFACE        "interface"
%token TOK_INTERSECT        "intersect"
%token TOK_JOIN_ANY         "join_any"
%token TOK_JOIN_NONE        "join_none"
%token TOK_LET              "let"
%token TOK_LOCAL            "local"
%token TOK_LOGIC            "logic"
%token TOK_LONGINT          "longint"
%token TOK_MATCHES          "matches"
%token TOK_MODPORT          "modport"
%token TOK_NETTYPE          "nettype"
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
%token TOK_REJECT_ON        "reject_on"
%token TOK_RESTRICT         "restrict"
%token TOK_RETURN           "return"
%token TOK_S_ALWAYS         "s_always"
%token TOK_S_EVENTUALLY     "s_eventually"
%token TOK_S_NEXTTIME       "s_nexttime"
%token TOK_S_UNTIL          "s_until"
%token TOK_S_UNTIL_WITH     "s_until_with"
%token TOK_SEQUENCE         "sequence"
%token TOK_SHORTINT         "shortint"
%token TOK_SHORTREAL        "shortreal"
%token TOK_SHOWCANCELLED    "showcancelled"
%token TOK_SOFT             "soft"
%token TOK_SOLVE            "solve"
%token TOK_STATIC           "static"
%token TOK_STRING           "string"
%token TOK_STRONG           "strong"
%token TOK_STRUCT           "struct"
%token TOK_SUPER            "super"
%token TOK_SYNC_ACCEPT_ON   "sync_accept_on"
%token TOK_SYNC_REJECT_ON   "sync_reject_on"
%token TOK_TAGGED           "tagged"
%token TOK_THIS             "this"
%token TOK_THROUGHOUT       "throughout"
%token TOK_TIMEPRECISION    "timeprecision"
%token TOK_TIMEUNIT         "timeunit"
%token TOK_TYPE             "type"
%token TOK_TYPEDEF          "typedef"
%token TOK_UNION            "union"
%token TOK_UNIQUE           "unique"
%token TOK_UNIQUE0          "unique0"
%token TOK_UNTIL            "until"
%token TOK_UNTIL_WITH       "until_with"
%token TOK_UNTYPED          "untyped"
%token TOK_VAR              "var"
%token TOK_VIRTUAL          "virtual"
%token TOK_VOID             "void"
%token TOK_WAIT_ORDER       "wait_order"
%token TOK_WEAK             "weak"
%token TOK_WILDCARD         "wildcard"
%token TOK_WITH             "with"
%token TOK_WITHIN           "within"

/* Others */
%token TOK_ENDOFFILE
%token TOK_NON_TYPE_IDENTIFIER
%token TOK_CLASS_IDENTIFIER
%token TOK_PACKAGE_IDENTIFIER
%token TOK_TYPE_IDENTIFIER
%token TOK_NUMBER           // number, any base
%token TOK_TIME_LITERAL     // number followed by time unit
%token TOK_QSTRING          // quoted string
%token TOK_SYSIDENT         // system task or function enable
%token TOK_SCANNER_ERROR

/* VL2SMV */
%token TOK_USING            "using"
%token TOK_PROVE            "prove"

// Precedence of System Verilog Assertions Operators,
// following System Verilog 1800-2017 Table 16-3.
// Bison expects these in order of increasing precedence,
// whereas the table gives them in decreasing order.
// The precendence of the assertion operators is lower than
// those in Table 11-2.
%nonassoc "property_expr_abort" // accept_on, reject_on, ...
%nonassoc "property_expr_clocking_event" // @(...) property_expr
%nonassoc "always" "s_always" "eventually" "s_eventually"
%nonassoc "accept_on" "reject_on"
%nonassoc "sync_accept_on" "sync_reject_on"
%right "|->" "|=>" "#-#" "#=#"
%nonassoc "until" "s_until" "until_with" "s_until_with" "implies"
%right "iff"
%left "or"
%left "and"
%nonassoc "not" "nexttime" "s_nexttime"
%left "intersect"
%left "within"
%right "throughout"
%left "##"
%nonassoc "[*" "[=" "[->"

// Precendence of Verilog operators,
// following System Verilog 1800-2017 Table 11-2.
// Bison expects these in order of increasing precedence,
// whereas the table gives them in decreasing order.
%nonassoc '{'
%nonassoc '=' "+=" "-=" "*=" "/=" "%=" "&=" "^=" "|=" "<<=" ">>=" "<<<=" ">>>=" ":=" ":/"
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
                { PARSER.parse_tree.add_item(stack_expr($1)); }
        | udp_declaration
                { PARSER.parse_tree.add_item(stack_expr($1)); }
        | interface_declaration
                { PARSER.parse_tree.add_item(stack_expr($1)); }
        | program_declaration
                { PARSER.parse_tree.add_item(stack_expr($1)); }
        | package_declaration
                { PARSER.parse_tree.add_item(stack_expr($1)); }
        | attribute_instance_brace package_item
                { add_attributes($2, $1);
                  PARSER.parse_tree.add_item(stack_expr($2)); }
        | attribute_instance_brace bind_directive
        | config_declaration
        ;

// This deviates from the IEEE 1800-2017 grammar
// to allow the module scope to be opened.
module_identifier_with_scope:
          module_identifier
          {
            $$ = $1;
            auto base_name = stack_expr($1).get(ID_base_name);
            push_scope(base_name, ".", verilog_scopet::MODULE);
          }
        ;

module_nonansi_header:
          attribute_instance_brace
          module_keyword
          module_identifier_with_scope
          package_import_declaration_brace
          parameter_port_list_opt
          list_of_ports_opt ';'
          {
            init($$); stack_expr($$).operands().resize(5);
            stack_expr($$).operands()[0].swap(stack_expr($1));
            stack_expr($$).operands()[1].swap(stack_expr($2));
            stack_expr($$).operands()[2].swap(stack_expr($3));
            stack_expr($$).operands()[3].swap(stack_expr($5));
            stack_expr($$).operands()[4].swap(stack_expr($6));
          }
        ;

module_ansi_header:
          attribute_instance_brace
          module_keyword
          module_identifier_with_scope
          package_import_declaration_brace
          parameter_port_list_opt
          list_of_port_declarations ';'
          {
            init($$); stack_expr($$).operands().resize(5);
            stack_expr($$).operands()[0].swap(stack_expr($1));
            stack_expr($$).operands()[1].swap(stack_expr($2));
            stack_expr($$).operands()[2].swap(stack_expr($3));
            stack_expr($$).operands()[3].swap(stack_expr($5));
            stack_expr($$).operands()[4].swap(stack_expr($6));
          }
        ;

module_declaration:
          module_nonansi_header module_item_brace TOK_ENDMODULE endmodule_identifier_opt
          {
            init($$);
            stack_expr($$) = PARSER.parse_tree.create_module(
              stack_expr($1).operands()[0],
              stack_expr($1).operands()[1],
              stack_expr($1).operands()[2],
              stack_expr($1).operands()[3],
              stack_expr($1).operands()[4],
              stack_expr($2));

            // close the module scope
            pop_scope();
          }
        | module_ansi_header module_item_brace TOK_ENDMODULE endmodule_identifier_opt
          {
            init($$);
            stack_expr($$) = PARSER.parse_tree.create_module(
              stack_expr($1).operands()[0],
              stack_expr($1).operands()[1],
              stack_expr($1).operands()[2],
              stack_expr($1).operands()[3],
              stack_expr($1).operands()[4],
              stack_expr($2));

            // close the module scope
            pop_scope();
          }
        | TOK_EXTERN module_nonansi_header
                /* ignored for now */
                { init($$); }
        | TOK_EXTERN module_ansi_header
                /* ignored for now */
                { init($$); }
        ;

module_keyword:
          TOK_MODULE { init($$, ID_module); }
        | TOK_MACROMODULE { init($$, ID_macromodule); }
        ;

interface_declaration:
          interface_nonansi_header
          timeunits_declaration_opt
          interface_item_brace
          TOK_ENDINTERFACE
                { $$ = $1; }
        ;

interface_nonansi_header:
          attribute_instance_brace
          TOK_INTERFACE
          lifetime_opt
          interface_identifier
                {
                  init($$, ID_verilog_interface);
                  stack_expr($$).set(ID_base_name, stack_expr($4).get(ID_base_name));
                }
          package_import_declaration_brace
          parameter_port_list_opt
          list_of_ports_opt
          ';'
                {
                  $$ = $5;
                }
        ;

program_declaration:
          TOK_PROGRAM TOK_ENDPROGRAM
        ;

checker_declaration:
          TOK_CHECKER { init($$); } checker_identifier
          checker_port_list_paren_opt ';'
          checker_or_generate_item_brace
          TOK_ENDCHECKER
                {
                  init($$);
                  irept attributes;
                  exprt parameter_port_list;
                  stack_expr($$) = verilog_parse_treet::create_module(
                    attributes, // attributes,
                    stack_expr($2), // module_keyword
                    stack_expr($3), // name
                    parameter_port_list, // parameter_port_list
                    stack_expr($4), // ports
                    stack_expr($6)  // module_items
                  );
                  stack_expr($$).id(ID_verilog_checker);
                }
        ;

checker_port_list_paren_opt:
          /* Optional */
                { init($$); }
        | '(' checker_port_list_opt ')'
                { $$ = $2; }
        ;

checker_port_list_opt:
          /* Optional */
                { init($$); }
        | checker_port_list
        ;

checker_port_list:
          checker_port_item
                { init($$); mts($$, $1); }
        | checker_port_list ',' checker_port_item
                { $$ = $1; mts($$, $3); }
        ;

checker_port_item:
          attribute_instance_brace
          checker_port_direction_opt
          property_formal_type
          formal_port_identifier
          variable_dimension_brace
                { init($$, ID_decl);
                  stack_expr($$).set(ID_class, stack_expr($2).id());
                  addswap($$, ID_type, $3);
                  mto($$, $4); /* declarator */
                }
        ;

checker_port_direction_opt:
          /* Optional */
                { init($$); }
        | TOK_INPUT
                { init($$, ID_input); }
        | TOK_OUTPUT
                { init($$, ID_output); }
        ;

class_declaration:
          TOK_CLASS any_identifier
          ';'
                {
                  init($$, ID_verilog_class);
                  auto base_name = stack_expr($2).get(ID_base_name);
                  stack_expr($$).set(ID_base_name, base_name);
                  push_scope(base_name, "::", verilog_scopet::CLASS);
                }
          class_item_brace
          TOK_ENDCLASS
                {
                  $$ = $4;
                  pop_scope();
                }
        ;

package_declaration:
          attribute_instance_brace TOK_PACKAGE
                { init($$, ID_verilog_package); }
          lifetime_opt
          any_identifier ';'
                {
                  push_scope(stack_expr($5).get(ID_base_name), "::", verilog_scopet::PACKAGE);
                }
          timeunits_declaration_opt
          package_item_brace
          TOK_ENDPACKAGE endpackage_identifier_opt
                {
                  pop_scope();
                  $$ = $3;
                  addswap($$, ID_module_items, $9);
                  stack_expr($$).set(ID_base_name, stack_expr($5).get(ID_base_name));
                }
        ;

endpackage_identifier_opt:
          /* Optional */
        | TOK_COLON package_identifier
        ;

timeunits_declaration_opt:
          /* Optional */
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

list_of_ports_opt:
        /* Optional */
              { make_nil($$); }
        | list_of_ports
        ;

list_of_ports: '(' port_brace ')' { $$ = $2; }
        ;

list_of_port_declarations: '(' ansi_port_declaration_brace ')' { $$=$2; }
        ;

ansi_port_declaration_brace:
          attribute_instance_brace ansi_port_declaration
                { init($$); mts($$, $2); }
        | ansi_port_declaration_brace ',' attribute_instance_brace ansi_port_declaration
                { $$=$1; mts($$, $4); }

          // append to last one -- required to make 
          // the grammar LR1
        | ansi_port_declaration_brace ',' port_identifier ansi_port_initializer_opt
                { $$=$1;
                  exprt decl(ID_decl);
                  decl.add_to_operands(std::move(stack_expr($3)));
                  // grab the type and class from previous!
                  const irept &prev=stack_expr($$).get_sub().back();
                  decl.set(ID_type, prev.find(ID_type));
                  decl.set(ID_class, prev.find(ID_class));
                  decl.set(ID_value, stack_expr($4));
                  stack_expr($$).move_to_sub(decl);
                }
        ;

port_declaration:
          attribute_instance_brace inout_declaration
                { add_attributes($2, $1); $$=$2; }
        | attribute_instance_brace input_declaration
                { add_attributes($2, $1); $$=$2; }
        | attribute_instance_brace output_declaration
                { add_attributes($2, $1); $$=$2; }
        ;

ansi_port_initializer_opt:
          /* Optional */
                { init($$, ID_nil); }
        | '=' expression
                { $$ = $2; }
        ;

ansi_port_declaration:
          net_port_header port_identifier unpacked_dimension_brace ansi_port_initializer_opt
                { init($$, ID_decl);
                  stack_expr($$).set(ID_class, to_unary_expr(stack_expr($1)).op().id());
                  // The data_type goes onto the declaration,
                  // and the unpacked_array_type goes onto the declarator.
                  stack_expr($$).type() = std::move(stack_expr($1).type());
                  addswap($2, ID_type, $3);
                  stack_expr($2).set(ID_value, stack_expr($4));
                  mto($$, $2); /* declarator */ }
        | variable_port_header port_identifier unpacked_dimension_brace ansi_port_initializer_opt
                { init($$, ID_decl);
                  if(to_unary_expr(stack_expr($1)).op().id() == ID_output)
                    stack_expr($$).set(ID_class, ID_output_register);
                  else
                    stack_expr($$).set(ID_class, to_unary_expr(stack_expr($1)).op().id());
                  // The data_type goes onto the declaration,
                  // and the unpacked_array_type goes onto the declarator.
                  stack_expr($$).type() = std::move(stack_expr($1).type());
                  addswap($2, ID_type, $3);
                  stack_expr($2).set(ID_value, stack_expr($4));
                  mto($$, $2); /* declarator */ }
        ;

net_port_header:
          port_direction net_port_type
                { init($$);
                  mto($$, $1);
                  addswap($$, ID_type, $2);
                }
        ;

variable_port_header:
        port_direction var_data_type
                { init($$);
                  mto($$, $1);
                  addswap($$, ID_type, $2);
                }
        ;

port_direction:
          TOK_INPUT
                { init($$, ID_input); }
        | TOK_OUTPUT
                { init($$, ID_output); }
        | TOK_INOUT
                { init($$, ID_inout); }
        | TOK_REF
                { init($$, ID_verilog_ref); }
        ;

// System Verilog standard 1800-2017
// A.1.4 Module items

module_common_item:
          module_or_generate_item_declaration
        | assertion_item
        | bind_directive
        | continuous_assign
        | initial_construct
        | final_construct
        | always_construct
        | loop_generate_construct
        | conditional_generate_construct
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
          attribute_instance_brace parameter_override
                { add_attributes($2, $1); $$=$2; }
        | attribute_instance_brace gate_instantiation
                { add_attributes($2, $1); $$=$2; }
        // UDP instances have the same syntax
        // as module instances; they only differ in the identifier.
        // | attribute_instance_brace udp_instantiation
        //      { add_attributes($2, $1); $$=$2; }
        | attribute_instance_brace module_instantiation
                { add_attributes($2, $1); $$=$2; }
        | attribute_instance_brace smv_using
                { add_attributes($2, $1); $$=$2; }
        | attribute_instance_brace smv_assume
                { add_attributes($2, $1); $$=$2; }
        | attribute_instance_brace module_common_item
                { add_attributes($2, $1); $$=$2; }
        // The next rule is not in 1800-2017, but is a vendor extension.
        | attribute_instance_brace system_tf_call ';'
                { add_attributes($2, $1); $$ = $2; }
        ;

module_or_generate_item_declaration:
          package_or_generate_item_declaration
        | genvar_declaration
        | clocking_declaration
        | TOK_DEFAULT TOK_CLOCKING clocking_identifier ';'
                { init($$, ID_verilog_default_clocking); mto($$, $3); }
        | TOK_DEFAULT TOK_DISABLE TOK_IFF expression_or_dist ';'
                { init($$, ID_verilog_default_disable); mto($$, $4); }
        ;

non_port_module_item:
          generate_region
        | module_or_generate_item
        | attribute_instance_brace specparam_declaration
                { add_attributes($2, $1); $$=$2; }
        | program_declaration
        | module_declaration
        | interface_declaration
        ;

// System Verilog standard 1800-2017
// A.1.5 Configuration source text

config_declaration:
           TOK_CONFIG config_identifier ';'
           local_parameter_declaration_opt
           design_statement
           config_rule_statement_opt
           TOK_ENDCONFIG config_identifier_opt
         ;

local_parameter_declaration_opt:
          /* Optional */
        | local_parameter_declaration ';'
        ;

design_statement:
          TOK_DESIGN design_identifier ';'
        ;

design_identifier:
          cell_identifier
        | library_identifier '.' cell_identifier
        ;

config_rule_statement_opt:
          /* Optional */
        | config_rule_statement
        ;

config_rule_statement:
          default_clause liblist_clause ';'
        | inst_clause liblist_clause ';'
        | inst_clause use_clause ';'
        | cell_clause liblist_clause ';'
        | cell_clause use_clause ';'
        ;

default_clause: TOK_DEFAULT;

inst_clause: TOK_INSTANCE inst_name;

inst_name: topmodule_identifier dot_instance_identifier_brace;

dot_instance_identifier_brace:
          /* Optional */
        | dot_instance_identifier_brace '.' instance_identifier
        ;

cell_clause:
          TOK_CELL cell_identifier
        | TOK_CELL library_identifier cell_identifier
        ;

liblist_clause: TOK_LIBLIST library_identifier_brace;

library_identifier_brace:
          /* Optional */
        | library_identifier_brace library_identifier
        ;

use_clause:
          TOK_USE cell_identifier colon_config_opt
        | TOK_USE library_identifier '.' cell_identifier colon_config_opt
        | TOK_USE '#' '(' named_parameter_assignment_brace ')' colon_config_opt
        | TOK_USE library_identifier '.' cell_identifier '#' '(' named_parameter_assignment_brace ')' colon_config_opt
        ;

colon_config_opt:
          /* Optional */
        | TOK_COLON TOK_CONFIG
        ;

config_identifier_opt:
          /* Optional */
        | TOK_COLON config_identifier
        ;

bind_directive:
          TOK_BIND
        ;

// System Verilog standard 1800-2017
// A.1.6 Interface items

interface_or_generate_item:
          attribute_instance_brace module_common_item
        | attribute_instance_brace extern_tf_declaration
        ;

extern_tf_declaration:
          TOK_EXTERN method_prototype ';'
        | TOK_EXTERN TOK_FORKJOIN task_prototype ';'
        ;

interface_item_brace:
          /* Optional */
        | interface_item_brace interface_item
        ;

interface_item:
          port_declaration ';'
        | non_port_interface_item
        ;

non_port_interface_item:
          generate_region
        | interface_or_generate_item
        | program_declaration
        /* | modport_declaration */
        | interface_declaration
        /* | timeunits_declaration */
        ;

// System Verilog standard 1800-2017
// A.1.9 Checker items

checker_or_generate_item_brace:
          /* Optional */
                { init($$); }
        | checker_or_generate_item_brace attribute_instance_brace checker_or_generate_item
                { $$ = $1; mts($$, $3); }
        ;

checker_or_generate_item:
          checker_or_generate_item_declaration
        | initial_construct
        | always_construct
        | final_construct
        | assertion_item
        | continuous_assign
        | checker_generate_item
        ;

checker_or_generate_item_declaration:
          data_declaration
        | function_declaration
        | checker_declaration
        | assertion_item_declaration
        | covergroup_declaration
        | genvar_declaration
        | clocking_declaration
        | TOK_DEFAULT TOK_CLOCKING clocking_identifier ';'
        | TOK_DEFAULT TOK_DISABLE TOK_IFF expression_or_dist ';'
        | ';'
        ;

checker_generate_item:
          loop_generate_construct
        | conditional_generate_construct
        | generate_region
        ;
        
// System Verilog standard 1800-2017
// A.1.9 Class items

class_item_brace:
          /* Optional */
        | class_item_brace class_item
        ;

// classes are yet to be implemented
class_item:
//        attribute_instance_brace class_property
//              { add_attributes($2, $1); $$=$2; }
//      | attribute_instance_brace class_method
//              { add_attributes($2, $1); $$=$2; }
          attribute_instance_brace class_constraint
                { add_attributes($2, $1); $$=$2; }
        | attribute_instance_brace class_declaration
                { add_attributes($2, $1); $$=$2; }
        | attribute_instance_brace covergroup_declaration
                { add_attributes($2, $1); $$=$2; }
        | local_parameter_declaration ';'
        | parameter_declaration ';'
        | ';'
        ;

class_property:
          property_qualifier_brace data_declaration
        | TOK_CONST class_item_qualifier_brace data_type identifier ';'
        | TOK_CONST class_item_qualifier_brace data_type identifier '=' constant_expression ';'
        ;

class_method:
          method_qualifier_brace task_declaration
        | method_qualifier_brace function_declaration
        | TOK_PURE TOK_VIRTUAL class_item_qualifier_brace method_prototype ';'
        | TOK_EXTERN method_qualifier_brace method_prototype ';'
        | method_qualifier_brace class_constructor_declaration
        | TOK_EXTERN method_qualifier_brace class_constructor_prototype
        ;

class_constructor_prototype:
          TOK_FUNCTION TOK_NEW ';'
        ;

class_constraint:
          constraint_prototype
        | constraint_declaration
        ;

class_item_qualifier_brace:
          /* Optional */
        | class_item_qualifier_brace class_item_qualifier
        ;

class_item_qualifier: TOK_STATIC | TOK_PROTECTED | TOK_LOCAL ;

property_qualifier_brace:
          /* Optional */
        | property_qualifier_brace property_qualifier
        ;

property_qualifier:
          random_qualifier
        | class_item_qualifier
        ;

random_qualifier_opt:
          /* Optional */
        | random_qualifier
        ;

random_qualifier:
          TOK_RAND
        | TOK_RANDC
        ;

method_qualifier_brace:
          /* Optional */
        | method_qualifier_brace method_qualifier
        ;

method_qualifier:
          TOK_PURE TOK_VIRTUAL
        | TOK_VIRTUAL
        | class_item_qualifier
        ;

method_prototype:
          task_prototype
        | function_prototype
        ;

class_constructor_declaration:
          TOK_FUNCTION TOK_NEW ';'
          block_item_declaration_brace
          TOK_ENDFUNCTION
        ;

// System Verilog standard 1800-2017
// A.1.10 Constraints

constraint_declaration:
          TOK_CONSTRAINT constraint_identifier constraint_block
        ;

constraint_block: '{' constraint_block_item_brace '}'
        ;

constraint_block_item_brace:
          /* Optional */
        | constraint_block_item_brace constraint_block_item
        ;

constraint_block_item:
          TOK_SOLVE ';'
        | constraint_expression
        ;

constraint_expression:
          expression_or_dist ';'
        ;

dist_list:
          dist_item
        | dist_list ',' dist_item
        ;

dist_item:
          value_range
        | value_range dist_weight
        ;

dist_weight:
          ":=" expression
        | ":/" expression
        ;

constraint_prototype: TOK_CONSTRAINT constraint_identifier ';'
        ;

// System Verilog standard 1800-2017
// A.1.11 Package items

package_item_brace:
          /* Optional */
                { init($$); }
        | package_item_brace package_item
                { $$ = $1; mts($$, $2); }
        ;

package_item:
          package_or_generate_item_declaration
//      | anonymous_program
//      | package_export_declaration
//      | timeunits_declaration
        ;

package_or_generate_item_declaration:
          net_declaration
        | data_declaration
        | task_declaration
        | function_declaration
        | checker_declaration
        | class_declaration
        | local_parameter_declaration ';'
        | parameter_declaration ';'
          /* The following rule is not in the standard.
             However, Section 11.12 explicitly states
             that let constructs may be declared in a
             module/interface/program/checker etc. */
        | let_declaration
        | covergroup_declaration
        | ';'
                { init($$, ID_verilog_empty_item); }
        | assertion_item_declaration
        ;

// System Verilog standard 1800-2017
// A.2.1.1 Module parameter declarations

local_parameter_declaration:
          TOK_LOCALPARAM data_type_or_implicit list_of_param_assignments
                { init($$, ID_local_parameter_decl);
                  stack_expr($$).type() = std::move(stack_type($2));
                  swapop($$, $3); }
        | TOK_LOCALPARAM TOK_TYPE list_of_type_assignments
                { init($$, ID_local_parameter_decl);
                  stack_expr($$).type() = typet(ID_type);
                  swapop($$, $3); }
        ;

parameter_declaration:
          TOK_PARAMETER data_type_or_implicit list_of_param_assignments
                { init($$, ID_parameter_decl);
                  stack_expr($$).type() = std::move(stack_type($2));
                  swapop($$, $3); }
        | TOK_PARAMETER TOK_TYPE list_of_type_assignments
                { init($$, ID_parameter_decl);
                  stack_expr($$).type() = typet(ID_type);
                  swapop($$, $3); }
        ;

specparam_declaration:
          TOK_SPECPARAM data_type_or_implicit list_of_specparam_assignments ';'
        ;

// System Verilog standard 1800-2017
// A.2.1.2 Port declarations

port_brace:
          port
                { init($$); mts($$, $1); }
        | port_brace ',' port
                { $$=$1;    mts($$, $3); }
        ;

port:     port_expression_opt
                { if(stack_expr($1).is_nil())
                    $$=$1;
                  else { init($$, ID_decl);  mto($$, $1); }
                }
        | '.' port_identifier '(' port_expression_opt ')'
                { init($$, ID_decl);
                  auto &decl = stack_expr($$);
                  decl.set(ID_class, ID_verilog_port_expression);
                  addswap($2, ID_value, $4);
                  decl.add_to_operands(std::move(stack_expr($2)));
                }
        ;

port_expression_opt:
          /* Optional */
          { make_nil($$); }
        | port_reference
        ;

port_reference:
          port_identifier
        | port_identifier constant_select  { make_nil($$); /* Not supported */ }
        | port_identifier part_select { make_nil($$); /* Not supported */ }
        ;

part_select:
          '[' const_expression TOK_COLON const_expression ']'
                { init($$, ID_verilog_non_indexed_part_select); mto($$, $2); mto($$, $4); }
        ;

// System Verilog standard 1800-2017
// A.2.1.3 Type declarations

// TOK_VAR is optional, but footnote 10 in IEEE 1800-2017 requires it
// when the data_type is omitted. We split the rule in the standard into two.
data_declaration:
          const_opt TOK_VAR lifetime_opt data_type_or_implicit list_of_variable_decl_assignments ';'
                { init($$, ID_decl);
                  stack_expr($$).set(ID_class, ID_var);
                  add_as_subtype(stack_type($1), stack_type($4));
                  addswap($$, ID_type, $1);
                  swapop($$, $5); }
        | const_opt lifetime_opt data_type list_of_variable_decl_assignments ';'
                { init($$, ID_decl);
                  stack_expr($$).set(ID_class, ID_reg);
                  add_as_subtype(stack_type($1), stack_type($3));
                  addswap($$, ID_type, $1);
                  swapop($$, $4); }
        | type_declaration
        | package_import_declaration
        | net_type_declaration
        ;

const_opt:
          /* Optional */
                { init($$, ID_nil); }
        | TOK_CONST
                { init($$, ID_const); stack_type($$).add_subtype().make_nil(); }
        ;

package_import_declaration_brace:
          /* Optional */
                { init($$); }
        | package_import_declaration_brace package_import_declaration
                { $$ = $1; mts($$, $2); }
        ;

package_import_declaration:
          TOK_IMPORT package_import_item_brace ';'
                { init($$, ID_verilog_package_import); swapop($$, $2); }
        ;

package_import_item_brace:
          package_import_item
                { init($$); mts($$, $1); }
        | package_import_item_brace ',' package_import_item
                { $$ = $1; mts($$, $3); }
        ;

package_import_item:
          package_identifier "::" identifier
                { init($$, ID_verilog_import_item);
                  auto base_name = stack_expr($1).id();
                  stack_expr($$).set(ID_verilog_package, base_name);
                  stack_expr($$).set(ID_base_name, stack_expr($3).id()); }
        | package_identifier "::" "*"
                { init($$, ID_verilog_import_item);
                  auto base_name = stack_expr($1).id();
                  stack_expr($$).set(ID_verilog_package, base_name);
                  stack_expr($$).set(ID_base_name, "*"); }
        ;

genvar_declaration:
          TOK_GENVAR list_of_genvar_identifiers ';'
                { init($$, ID_verilog_generate_decl); swapop($$, $2); }
        ;

net_declaration:
          net_type drive_strength_opt vectored_scalared_opt data_type_or_implicit delay3_opt list_of_net_decl_assignments ';'
                { init($$, ID_decl);
                  addswap($$, ID_class, $1);
                  addswap($$, ID_type, $4);
                  swapop($$, $6); }
        | TOK_INTERCONNECT delay3_opt list_of_net_decl_assignments ';'
                { init($$, ID_decl);
                  stack_expr($$).set(ID_class, ID_verilog_interconnect);
                  swapop($$, $3); }
        ;

// Note that the identifier that is defined using the typedef may be
// an existing type or non-type identifier.
type_declaration:
          TOK_TYPEDEF
                { init($$, ID_decl);
                  stack_expr($$).set(ID_class, ID_typedef);
                }
           data_type any_identifier ';'
                { $$ = $2;
                  // add to the scope as a type name
                  PARSER.scopes.add_name(stack_expr($4).get(ID_base_name), "", verilog_scopet::TYPEDEF);
                  addswap($$, ID_type, $3);
                  stack_expr($4).id(ID_declarator);
                  mto($$, $4);
                }
        ;

net_type_declaration:
          TOK_NETTYPE
                { init($$, ID_decl);
                  stack_expr($$).set(ID_class, ID_typedef);
                }
          data_type any_identifier ';'
                { $$ = $2;
                  // add to the scope as a type name
                  PARSER.scopes.add_name(stack_expr($4).get(ID_base_name), "", verilog_scopet::TYPEDEF);
                  addswap($$, ID_type, $3);
                  stack_expr($4).id(ID_declarator);
                  mto($$, $4);
                }
        ;

vectored_scalared_opt:
          /* Optional */
                { make_nil($$); }
        | TOK_VECTORED     { init($$, "vectored"); }
        | TOK_SCALARED     { init($$, "scalared"); }
        ;

list_of_net_decl_assignments:
          net_decl_assignment
                { init($$); mto($$, $1); }
        | list_of_net_decl_assignments ',' net_decl_assignment
                { $$=$1;    mto($$, $3); }
        ;

lifetime_opt:
          /* optional */
                { init($$); }
        | lifetime
        ;

lifetime:
          TOK_STATIC { init($$, ID_static); }
        | TOK_AUTOMATIC { init($$, ID_automatic); }
        ;

// System Verilog standard 1800-2017
// A.2.2.1 Net and variable types

casting_type:
          simple_type
                {
                  init($$, ID_verilog_explicit_type_cast);
                  stack_expr($$).type() = stack_type($1);
                }
        | constant_primary
                { init($$, ID_verilog_explicit_size_cast); mto($$, $1); }
        | signing
                {
                  init($$, ID_verilog_explicit_signing_cast);
                  stack_expr($$).type() = stack_type($1);
                }
        | TOK_STRING
                {
                  init($$, ID_verilog_explicit_type_cast);
                  stack_expr($$).type() = stack_type($1);
                }
        | TOK_CONST
                {
                  init($$, ID_verilog_explicit_const_cast);
                  stack_expr($$).type() = stack_type($1);
                }
        ;

data_type:
          integer_vector_type signing_opt packed_dimension_brace
                {
                  // The integer type is a subtype of the signing.
                  add_as_subtype(stack_type($2), stack_type($1));
                  // That becomes a subtype of the packed dimension.
                  add_as_subtype(stack_type($3), stack_type($2));
                  $$ = $3;
                }
        | integer_atom_type signing_opt
                {
                  // The integer type is a subtype of the signing.
                  add_as_subtype(stack_type($2), stack_type($1));
                  $$ = $2;
                }
        | non_integer_type
        | struct_union packed_opt signing_opt 
          '{' struct_union_member_brace '}' packed_dimension_brace
                { $$=$1;
                  if(stack_expr($2).id() == ID_packed)
                    stack_type($1).set(ID_packed, true);
                  addswap($$, ID_declaration_list, $5); }
        | TOK_ENUM enum_base_type_opt '{' enum_name_declaration_list '}'
                { // Like in C, these do _not_ create a scope.
                  // The enum names go into the current scope.
                  init($$, ID_verilog_enum);
                  stack_type($$).add_subtype() = std::move(stack_type($2));
                  stack_type($$).set(ID_enum_names, stack_type($4));

                  // We attach a dummy id to distinguish two syntactically
                  // identical enum types.
                  stack_expr($$).set(ID_base_name, "enum-" + PARSER.get_next_id());
                  stack_expr($$).set(ID_verilog_scope_prefix, PARSER.scopes.current_scope().prefix);
                }
        | TOK_STRING
                { init($$, ID_verilog_string); }
        | TOK_CHANDLE
                { init($$, ID_verilog_chandle); }
        | TOK_VIRTUAL interface_opt interface_identifier
                { init($$, "virtual_interface"); }
        | type_identifier packed_dimension_brace
                { add_as_subtype(stack_type($2), stack_type($1));
                  $$ = $2; }
        | package_scope type_identifier packed_dimension_brace
                { mto($1, $2);
                  add_as_subtype(stack_type($3), stack_type($1));
                  $$ = $3; }
        | class_type
        | TOK_EVENT
                { init($$, ID_verilog_event); }
        /*
        | ps_covergroup_identifier
        */
        | type_reference
        ;
        
enum_name_value_opt:
          /* optional */
          {
            init($$, ID_nil);
          }
        | '=' constant_expression { $$ = $2; }
        ;

enum_name_declaration:
          any_identifier enum_name_value_opt
          {
            init($$);
            auto &scope = PARSER.scopes.add_name(stack_expr($1).get(ID_base_name), "", verilog_scopet::ENUM_NAME);
            stack_expr($$).set(ID_base_name, scope.base_name());
            stack_expr($$).set(ID_verilog_scope_prefix, scope.parent->prefix);
            stack_expr($$).add(ID_value).swap(stack_expr($2));
          }
        ;
        
enum_name_declaration_list:
          enum_name_declaration
                { init($$); mts($$, $1); }
        | enum_name_declaration_list ',' enum_name_declaration
                { $$=$1; mts($$, $3); }
        ;

class_scope: class_type TOK_COLONCOLON
        ;

class_scope_opt:
          /* Optional */
        | class_scope
        ;

integer_type:
          integer_vector_type
        | integer_atom_type
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
        | TOK_INTEGER { init($$, ID_verilog_integer); }
        | TOK_TIME { init($$, ID_verilog_time); }
        ;
        
class_type: class_identifier
        ;
        
struct_union_member_brace:
          /* Not optional! No empty structs. */
          struct_union_member
                { init($$); mts($$, $1); }
        | struct_union_member_brace struct_union_member
                { $$=$1; mts($$, $2); }
        ;

struct_union_member:
          attribute_instance_brace
          random_qualifier_opt
          data_type_or_void
          list_of_variable_decl_assignments ';'
                { $$=$4;
                  stack_expr($$).id(ID_decl);
                  addswap($$, ID_type, $3);
                  add_attributes($$, $1); }
        ;
        
enum_base_type_opt:
          /* Optional */
                { init($$, ID_nil); }
        | integer_atom_type signing_opt
                {
                  // The integer type is a subtype of the signing.
                  add_as_subtype(stack_type($2), stack_type($1));
                  $$ = $1;
                }
        | integer_vector_type signing_opt packed_dimension_opt
                {
                  // The integer type is a subtype of the signing.
                  add_as_subtype(stack_type($2), stack_type($1));
                  // That becomes a subtype of the packed dimension.
                  add_as_subtype(stack_type($3), stack_type($2));
                  $$ = $3;
                }
        | type_identifier packed_dimension_opt
                { $$ = $2; add_as_subtype(stack_type($$), stack_type($1)); }
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

net_type_opt:
          /* Optional */
                { init($$, ID_nil); }
        | net_type
        ;

net_port_type:
          net_type_opt signing_opt packed_dimension_brace
        {
          // The net type is a subtype of the signing.
          add_as_subtype(stack_type($2), stack_type($1));
          // That becomes a subtype of the packed dimension.
          add_as_subtype(stack_type($3), stack_type($2));
          $$ = $3;
        }
        | TOK_INTERCONNECT
        {
          init($$, ID_verilog_interconnect);
        }
        ;

variable_port_type: var_data_type ;

var_data_type:
          data_type
        | TOK_VAR data_type_or_implicit { $$ = $2; }
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

simple_type:
          integer_type
        | non_integer_type
        | ps_type_identifier
//      | ps_parameter_identifier
        ;

data_type_or_void:
          data_type
        | TOK_VOID
                { init($$, ID_verilog_void); }
        ;

type_reference:
          TOK_TYPE '(' expression ')'
                { init($$, ID_verilog_type_reference); mto($$, $3); }
        | TOK_TYPE '(' data_type ')'
                { init($$, ID_verilog_type_reference); addswap($$, ID_type_arg, $3); }
        ;

// System Verilog standard 1800-2017
// A.2.2.2 Strengths

drive_strength_opt:
          /* Optional */ { make_nil($$); }
//      | drive_strength
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
          // must be any_identifier to allow re-use of typedef identifiers
          any_identifier
                { init($$);
                  PARSER.scopes.add_name(stack_expr($1).get(ID_base_name), "", verilog_scopet::OTHER);
                  stack_expr($1).id(ID_declarator);
                  mto($$, $1);
                }
          // must be any_identifier to allow re-use of typedef identifiers
        | list_of_genvar_identifiers ',' any_identifier
                { $$=$1;
                  PARSER.scopes.add_name(stack_expr($3).get(ID_base_name), "", verilog_scopet::OTHER);
                  stack_expr($3).id(ID_declarator);
                  mto($$, $3);
                }
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

list_of_variable_identifiers:
          variable_identifier
                { init($$);
                  stack_expr($1).id(ID_declarator);
                  mto($$, $1); }
        | list_of_variable_identifiers ',' variable_identifier
                { $$=$1;
                  stack_expr($3).id(ID_declarator);
                  mto($$, $3); }
        ;

// This rule is more permissive that the grammar in the standard
// to cover list_of_param_assignments.
parameter_port_declaration:
          TOK_PARAMETER data_type_or_implicit param_assignment
                { init($$, ID_decl); stack_expr($$).type() = std::move(stack_type($2)); mto($$, $3); }
        | TOK_PARAMETER TOK_TYPE type_assignment
                { init($$, ID_decl); stack_expr($$).type() = typet{ID_type}; mto($$, $3); }
        | TOK_LOCALPARAM data_type_or_implicit param_assignment
                { init($$, ID_decl); stack_expr($$).type() = std::move(stack_type($2)); mto($$, $3); }
        | TOK_LOCALPARAM TOK_TYPE type_assignment
                { init($$, ID_decl); stack_expr($$).type() = typet{ID_type}; mto($$, $3); }
        | data_type param_assignment
                { init($$, ID_decl); stack_expr($$).type() = std::move(stack_type($1)); mto($$, $2); }
        | param_assignment
                { init($$, ID_decl); mto($$, $1); }
        | TOK_TYPE type_assignment
                { init($$, ID_decl); stack_expr($$).type() = typet{ID_type}; mto($$, $2); }
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

param_assignment: param_identifier '=' constant_param_expression
                { init($$, ID_parameter);
                  auto base_name = stack_expr($1).get(ID_base_name);
                  stack_expr($$).set(ID_base_name, base_name);
                  addswap($$, ID_value, $3); }
        ;

list_of_type_assignments:
          type_assignment
                { init($$); mto($$, $1); }
        | list_of_type_assignments ',' type_assignment
                { $$=$1;    mto($$, $3); }
        ;

type_assignment: param_identifier '=' data_type
                { init($$, ID_declarator);
                  auto base_name = stack_expr($1).get(ID_base_name);
                  stack_expr($$).set(ID_base_name, base_name);
                  stack_expr($$).set(ID_value, type_exprt{stack_type($3)});
                  stack_expr($$).type() = typet{ID_type};

                  // add to the scope as a type name
                  PARSER.scopes.add_name(base_name, "", verilog_scopet::TYPEDEF);
                }
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
          TOK_INPUT net_port_type list_of_port_identifiers
                { init($$, ID_decl);
                  stack_expr($$).set(ID_class, ID_input);
                  addswap($$, ID_type, $2);
                  swapop($$, $3); }
        | TOK_INPUT variable_port_type list_of_variable_identifiers
                { init($$, ID_decl);
                  stack_expr($$).set(ID_class, ID_input);
                  addswap($$, ID_type, $2);
                  swapop($$, $3); }
        ;

output_declaration:
          TOK_OUTPUT net_port_type list_of_port_identifiers
                { init($$, ID_decl);
                  stack_expr($$).set(ID_class, ID_output);
                  addswap($$, ID_type, $2);
                  swapop($$, $3); }
        | TOK_OUTPUT variable_port_type list_of_port_identifiers
                { init($$, ID_decl);
                  stack_expr($$).set(ID_class, ID_output_register);
                  addswap($$, ID_type, $2);
                  swapop($$, $3); }
        ;

inout_declaration:
          TOK_INOUT net_port_type list_of_port_identifiers
                { init($$, ID_decl);
                  stack_expr($$).set(ID_class, ID_inout);
                  addswap($$, ID_type, $2);
                  swapop($$, $3); }
        ;

signing_opt:
          /* Optional */
                { make_nil($$); } 
        | signing
        ;

signing:
          TOK_SIGNED
                { init($$, ID_signed);
                  stack_type($$).add_subtype().make_nil(); }
        | TOK_UNSIGNED
                { init($$, ID_unsigned);
                  stack_type($$).add_subtype().make_nil(); }
        ;

automatic_opt:
          /* Optional */
                { make_nil($$); } 
        | TOK_AUTOMATIC
                { init($$, ID_automatic); }
        ;

list_of_port_identifiers:
          port_identifier unpacked_dimension_brace
                { init($$);
                  stack_expr($1).id(ID_declarator);
                  addswap($1, ID_type, $2);
                  mto($$, $1); }
        | list_of_port_identifiers ',' port_identifier unpacked_dimension_brace
                { $$=$1;
                  stack_expr($3).id(ID_declarator);
                  addswap($3, ID_type, $4);
                  mto($$, $3); }
        ;

range_opt:
                { make_nil($$); }
        | range
        ;

range:  part_select;

// System Verilog standard 1800-2017
// A.2.4 Declaration assignments

net_decl_assignment:
          net_identifier unpacked_dimension_brace
                { $$ = $1;
                  stack_expr($$).id(ID_declarator);
                  addswap($$, ID_type, $2); }
        | net_identifier unpacked_dimension_brace '=' expression
                { $$ = $1;
                  stack_expr($$).id(ID_declarator);
                  addswap($$, ID_type, $2);
                  addswap($$, ID_value, $4); }
        ;

variable_decl_assignment:
          variable_identifier variable_dimension_brace
                { $$ = $1; stack_expr($$).id(ID_declarator); addswap($$, ID_type, $2); }
        | variable_identifier variable_dimension_brace '=' expression
                { $$ = $1; stack_expr($$).id(ID_declarator);
                  addswap($$, ID_type, $2);
                  addswap($$, ID_value, $4); }
        | variable_identifier variable_dimension_brace '=' class_new
                { $$ = $1; stack_expr($$).id(ID_declarator);
                  addswap($$, ID_type, $2);
                  addswap($$, ID_value, $4); }
        ;

class_new:
          TOK_NEW list_of_arguments_paren_opt
                { init($$, ID_verilog_new); mto($$, $2); }
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

packed_dimension_opt:
          /* Optional */
                { init($$, ID_nil); }
        | packed_dimension
        ;

packed_dimension:
          '[' const_expression TOK_COLON const_expression ']'
                { init($$, ID_verilog_packed_array);
                  stack_type($$).add_subtype().make_nil();
                  exprt &range=static_cast<exprt &>(stack_type($$).add(ID_range));
                  range.add_to_operands(stack_expr($2));
                  range.add_to_operands(stack_expr($4)); }
        | unsized_dimension
        ;

associative_dimension:
          '[' data_type ']'
                { init($$, ID_verilog_associative_array);
                  // for the element type
                  stack_type($$).add_subtype().make_nil();
                }
        | '[' '*' ']'
                { init($$, ID_verilog_associative_array);
                  // for the element type
                  stack_type($$).add_subtype().make_nil();
                }
        | "[*" ']'
                { init($$, ID_verilog_associative_array);
                  // for the element type
                  stack_type($$).add_subtype().make_nil();
                }
        ;

unpacked_dimension:
          '[' const_expression TOK_COLON const_expression ']'
                { init($$, ID_verilog_unpacked_array);
                  stack_type($$).add_subtype().make_nil();
                  exprt &range=static_cast<exprt &>(stack_type($$).add(ID_range));
                  range.add_to_operands(stack_expr($2));
                  range.add_to_operands(stack_expr($4)); }
        | '[' expression ']'
                { // starts at index 0
                  init($$, ID_verilog_unpacked_array);
                  stack_type($$).add_subtype().make_nil();
                  stack_type($$).set(ID_size, std::move(stack_expr($2)));
                }
        ;

variable_dimension:
          unsized_dimension
        | unpacked_dimension
        | associative_dimension
        | queue_dimension
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

queue_dimension:
          '[' '$' ']'
                { init($$, ID_verilog_queue); stack_type($$).add_subtype().make_nil(); }
        | '[' '$' TOK_COLON constant_expression ']'
                { init($$, ID_verilog_queue); stack_type($$).add_subtype().make_nil(); }
        ;

unsized_dimension: '[' ']'
                { init($$, "unsized"); }
        ;

struct_union:
          TOK_STRUCT { init($$, ID_struct); }
        | TOK_UNION { init($$, ID_union); }
        | TOK_UNION TOK_TAGGED { init($$, ID_union); }
        ;
        
// System Verilog standard 1800-2017
// A.2.6 Function declarations

function_data_type_or_implicit:
          data_type_or_void
        | implicit_data_type
        ;

function_declaration: TOK_FUNCTION lifetime_opt function_body_declaration
                { $$ = $3; addswap($$, ID_verilog_lifetime, $2); }
        ;

function_body_declaration:
          function_data_type_or_implicit
          function_identifier
                { push_scope(stack_expr($2).get(ID_base_name), ".", verilog_scopet::FUNCTION); }
          ';'
          tf_item_declaration_brace
          function_statement_or_null_brace
          TOK_ENDFUNCTION
                { init($$, ID_verilog_function_decl);
                  addswap($$, ID_type, $1);
                  add_as_subtype(stack_type($1), stack_type($1));
                  addswap($$, ID_symbol, $2);
                  addswap($$, ID_verilog_declarations, $5);
                  addswap($$, ID_body, $6);
                  pop_scope();
                }
        | function_data_type_or_implicit
          function_identifier
                { push_scope(stack_expr($2).get(ID_base_name), ".", verilog_scopet::FUNCTION); }
          '(' tf_port_list_opt ')' ';'
          block_item_declaration_brace
          function_statement_or_null_brace
          TOK_ENDFUNCTION
                { init($$, ID_verilog_function_decl);
                  addswap($$, ID_type, $1);
                  add_as_subtype(stack_type($1), stack_type($1));
                  addswap($$, ID_symbol, $2);
                  addswap($$, ID_ports, $5);
                  addswap($$, ID_verilog_declarations, $8);
                  addswap($$, ID_body, $9);
                  pop_scope();
                }
        ;

tf_item_declaration_brace:
          /* Optional */
                { init($$); }
        | tf_item_declaration_brace tf_item_declaration
                { $$=$1; mts($$, $2); }
        ;

tf_item_declaration:
          block_item_declaration
        | attribute_instance_brace input_declaration ';'
                { add_attributes($2, $1); $$ = $2; }
        | attribute_instance_brace output_declaration ';'
                { add_attributes($2, $1); $$ = $2; }
        | attribute_instance_brace inout_declaration ';'
                { add_attributes($2, $1); $$ = $2; }
        ;

function_prototype: TOK_FUNCTION data_type_or_void function_identifier
        ;

// System Verilog standard 1800-2017
// A.2.7 Task declarations

task_declaration:
          TOK_TASK task_identifier
                { push_scope(stack_expr($2).get(ID_base_name), ".", verilog_scopet::TASK); }
          ';'
          tf_item_declaration_brace
          task_statement_or_null_brace
          TOK_ENDTASK
                { init($$, ID_verilog_task_decl);
                  addswap($$, ID_symbol, $2);
                  addswap($$, ID_verilog_declarations, $5);
                  addswap($$, ID_body, $6);
                  pop_scope();
                }
        | TOK_TASK task_identifier
                { push_scope(stack_expr($2).get(ID_base_name), ".", verilog_scopet::TASK); }
          '(' tf_port_list_opt ')' ';'
          tf_item_declaration_brace
          task_statement_or_null_brace
          TOK_ENDTASK
                { init($$, ID_verilog_task_decl);
                  addswap($$, ID_symbol, $2);
                  addswap($$, ID_ports, $5);
                  addswap($$, ID_verilog_declarations, $8);
                  addswap($$, ID_body, $9);
                  pop_scope();
                }
        ;

task_statement_or_null_brace:
          statement_or_null
                { init($$); mto($$, $1); }
        | task_statement_or_null_brace statement_or_null
                { $$ = $1; mto($$, $2); }
        ;

task_prototype: TOK_TASK task_identifier
        ;

tf_port_list_paren_opt:
          /* Optional */
                { init($$); }
        | '(' tf_port_list_opt ')'
                { $$ = $2; }
        ;

tf_port_list_opt:
        /* Optional */
                { init($$); }
        | tf_port_list
        ;

tf_port_list:
          tf_port_item
                { init($$); mts($$, $1); }
        | tf_port_list ',' tf_port_item
                { $$ = $1; mts($$, $3); }
        ;

tf_port_item:
          attribute_instance_brace
          tf_port_direction_opt
          data_type_or_implicit
          port_identifier
          variable_dimension_brace
                { init($$, ID_decl);
                  add_attributes($$, $1);
                  addswap($$, ID_class, $2);
                  addswap($$, ID_type, $3);
                  stack_expr($4).id(ID_declarator);
                  mto($$, $4); }
        ;

tf_port_direction_opt:
          /* Optional */
        | port_direction
        | TOK_CONST TOK_REF
                { $$ = $2; }
        ;

// System Verilog standard 1800-2017
// A.2.8 Block item declarations

block_item_declaration:
          attribute_instance_brace data_declaration
                { add_attributes($2, $1); $$=$2; }
        | attribute_instance_brace local_parameter_declaration ';'
                { add_attributes($2, $1); $$=$2; }
        | attribute_instance_brace parameter_declaration ';'
                { add_attributes($2, $1); $$=$2; }
        | attribute_instance_brace let_declaration
                { add_attributes($2, $1); $$=$2; }
        ;

// System Verilog standard 1800-2017
// A.2.10 Assertion declarations

concurrent_assertion_item:
          concurrent_assertion_statement
        | block_identifier TOK_COLON concurrent_assertion_statement
                {
                  $$=$3;
                  auto base_name = stack_expr($1).get(ID_base_name);
                  stack_expr($$).set(ID_base_name, base_name);
                }
        ;

concurrent_assertion_statement:
          assert_property_statement
        | assume_property_statement
        | cover_property_statement
        | cover_sequence_statement
        | restrict_property_statement
        ;

/* This one mimicks functionality in Cadence SMV */
smv_assertion_statement:
          TOK_ASSERT property_identifier TOK_COLON smv_property ';'
                { init($$, ID_verilog_smv_assert); stack_expr($$).operands().resize(2);
                  to_binary_expr(stack_expr($$)).op0().swap(stack_expr($4));
                  to_binary_expr(stack_expr($$)).op1().make_nil();
                  auto base_name = stack_expr($2).get(ID_base_name);
                  stack_expr($$).set(ID_base_name, base_name);
                }
        | TOK_ASSUME property_identifier TOK_COLON smv_property ';'
                { init($$, ID_verilog_smv_assume); stack_expr($$).operands().resize(2);
                  to_binary_expr(stack_expr($$)).op0().swap(stack_expr($4));
                  to_binary_expr(stack_expr($$)).op1().make_nil();
                  auto base_name = stack_expr($2).get(ID_base_name);
                  stack_expr($$).set(ID_base_name, base_name);
                }
        ;

smv_property_identifier_list:
          non_type_identifier
        | smv_property_identifier_list ',' non_type_identifier
        ;

smv_using:
          TOK_USING smv_property_identifier_list TOK_PROVE smv_property_identifier_list ';'
                { init($$, ID_verilog_smv_using); }
        ;

smv_assume:
          TOK_ASSUME smv_property_identifier_list ';'
                { init($$, ID_verilog_smv_assume); }
        ;

// We use smv_property_proper vs smv_property to avoid the reduce/reduce
// conflict that arises between '(' expression ')' and '(' smv_property ')'.
smv_property:
          smv_property_proper
        | expression
        ;

smv_property_proper:
          TOK_EVENTUALLY smv_property
                { init($$, ID_verilog_smv_eventually); mto($$, $2); }
        | '(' smv_property_proper ')'
                { $$ = $2; }
        ;

assert_property_statement:
          TOK_ASSERT TOK_PROPERTY '(' property_spec ')' action_block
                { init($$, ID_verilog_assert_property); mto($$, $4); mto($$, $6); }
        ;

assume_property_statement:
          TOK_ASSUME TOK_PROPERTY '(' property_spec ')' action_block
                { init($$, ID_verilog_assume_property); mto($$, $4); mto($$, $6); }
        ;

cover_property_statement: TOK_COVER TOK_PROPERTY '(' property_spec ')' action_block
                { init($$, ID_verilog_cover_property); mto($$, $4); mto($$, $6); }
        ;

cover_sequence_statement:
          TOK_COVER TOK_SEQUENCE '(' sequence_expr ')' action_block
                { init($$, ID_verilog_cover_sequence); mto2($$, $4, $6); }
        | TOK_COVER TOK_SEQUENCE '(' clocking_event TOK_DISABLE TOK_IFF '(' expression ')' sequence_expr ')' action_block
                { init($5, ID_sva_sequence_disable_iff); mto2($5, $8, $10); init($$, ID_verilog_cover_sequence); mto2($$, $5, $12); }
        | TOK_COVER TOK_SEQUENCE '(' TOK_DISABLE TOK_IFF '(' expression ')' sequence_expr ')' action_block
                { init($4, ID_sva_sequence_disable_iff); mto2($4, $7, $9); init($$, ID_verilog_cover_sequence); mto2($$, $4, $11); }
        ;

restrict_property_statement: TOK_RESTRICT TOK_PROPERTY '(' property_spec ')' ';'
                { init($$, ID_verilog_restrict_property); mto($$, $4); mto($$, $6); }
        ;

expect_property_statement: TOK_EXPECT '(' property_spec ')' action_block
                { init($$, ID_verilog_expect_property); mto($$, $3); mto($$, $5); }
        ;

assertion_item_declaration:
          property_declaration
        | sequence_declaration
        ;

property_declaration:
          TOK_PROPERTY any_identifier
                { auto base_name = stack_expr($2).get(ID_base_name);
                  push_scope(base_name, ".", verilog_scopet::PROPERTY); }
          property_port_list_paren_opt ';'
          property_spec semicolon_opt
          TOK_ENDPROPERTY property_identifier_opt
                { init($$, ID_verilog_property_declaration);
                  auto base_name = stack_expr($2).get(ID_base_name);
                  stack_expr($$).set(ID_base_name, base_name);
                  mto($$, $6);
                  pop_scope();
                }
        ;

property_identifier_opt:
          /* optional */
        | TOK_COLON property_identifier
        ;

property_port_list_paren_opt:
          /* optional */
        | '(' property_port_list_opt ')'
        ;

property_port_list_opt:
          /* optional */
        | property_port_list
        ;

property_port_list:
          property_port_item
        | property_port_list_opt ',' property_port_item
        ;

property_port_item:
          attribute_instance_brace property_formal_type formal_port_identifier variable_dimension_brace
        ;

property_formal_type:
          sequence_formal_type
        | TOK_PROPERTY
        ;

property_spec:
          clocking_event TOK_DISABLE TOK_IFF '(' expression ')' property_expr
                { init($$, ID_sva_disable_iff); mto($$, $5); mto($$, $7); }
        | TOK_DISABLE TOK_IFF '(' expression ')' property_expr
                { init($$, ID_sva_disable_iff); mto($$, $4); mto($$, $6); }
        | property_expr
        ;

sequence_formal_type:
          data_type
        | TOK_SEQUENCE
                { init($$, ID_verilog_sequence); }
        | TOK_UNTYPED
                { init($$, ID_verilog_untyped); }
        ;

// The 1800-2017 grammar has an ambiguity where
// '(' expression ')' can either be an expression or a property_expr,
// which yields a reduce/reduce conflict. Hence, we split the rules
// for property_expr into property_expr and property_expr_proper.

property_expr:
          expression_or_dist
        | property_expr_proper
        ;

// To allow the operators and/or to be used as either sequence or property,
// we use 'property_expr' where 'sequence_expr' would be required, and
// copy the sequence_expr rules.
property_expr_proper:
          "strong" '(' sequence_expr ')'
                { init($$, ID_sva_strong); mto ($$, $3); }
        | "weak" '(' sequence_expr ')'
                { init($$, ID_sva_weak); mto ($$, $3); }
        | '(' property_expr_proper ')'
                { $$ = $2; }
        | "not" property_expr
                { init($$, ID_sva_not); mto($$, $2); }
        | property_expr "or" property_expr
                { init($$, ID_sva_or); mto($$, $1); mto($$, $3); }
        | property_expr "and" property_expr
                { init($$, ID_sva_and); mto($$, $1); mto($$, $3); }
        // requires sequence_expr on the LHS
        | property_expr "|->" property_expr
                { init($$, ID_sva_overlapped_implication); mto($$, $1); mto($$, $3); }
        // requires sequence_expr on the LHS
        | property_expr "|=>" property_expr
                { init($$, ID_sva_non_overlapped_implication); mto($$, $1); mto($$, $3); }
        | "if" '(' expression_or_dist ')' property_expr %prec LT_TOK_ELSE
                { init($$, ID_sva_if); mto($$, $3); mto($$, $5); stack_expr($$).add_to_operands(nil_exprt()); }
        | "if" '(' expression_or_dist ')' property_expr "else" property_expr
                { init($$, ID_sva_if); mto($$, $3); mto($$, $5); mto($$, $7); }
        | "case" '(' expression_or_dist ')' property_case_item_brace "endcase"
                { init($$, ID_sva_case); mto($$, $3); mto($$, $5); }
        // requires sequence_expr on the LHS
        | property_expr "#-#" property_expr
                { init($$, ID_sva_overlapped_followed_by); mto($$, $1); mto($$, $3); }
        // requires sequence_expr on the LHS
        | property_expr "#=#" property_expr
                { init($$, ID_sva_nonoverlapped_followed_by); mto($$, $1); mto($$, $3); }
        | "nexttime" property_expr
                { init($$, ID_sva_nexttime); mto($$, $2); }
        | "nexttime" '[' constant_expression ']' property_expr %prec "nexttime"
                { init($$, ID_sva_indexed_nexttime); mto($$, $3); mto($$, $5); }
        | "s_nexttime" property_expr
                { init($$, ID_sva_s_nexttime); mto($$, $2); }
        | "s_nexttime" '[' constant_expression ']' property_expr %prec "s_nexttime"
                { init($$, ID_sva_indexed_s_nexttime); mto($$, $3); mto($$, $5); }
        | "always" '[' cycle_delay_const_range_expression ']' property_expr %prec "always"
                { init($$, ID_sva_ranged_always); swapop($$, $3); mto($$, $5); }
        | "always" property_expr
                { init($$, ID_sva_always); mto($$, $2); }
        | "s_always" '[' constant_range ']' property_expr %prec "s_always"
                { init($$, ID_sva_s_always); swapop($$, $3); mto($$, $5); }
        | "s_eventually" property_expr
                { init($$, ID_sva_s_eventually); mto($$, $2); }
        | "eventually" '[' constant_range ']' property_expr %prec "eventually"
                { init($$, ID_sva_eventually); swapop($$, $3); mto($$, $5); }
        | "s_eventually" '[' cycle_delay_const_range_expression ']' property_expr %prec "s_eventually"
                { init($$, ID_sva_ranged_s_eventually); swapop($$, $3); mto($$, $5); }
        | property_expr "until" property_expr
                { init($$, ID_sva_until); mto($$, $1); mto($$, $3); }
        | property_expr "s_until" property_expr
                { init($$, ID_sva_s_until); mto($$, $1); mto($$, $3); }
        | property_expr "until_with" property_expr
                { init($$, ID_sva_until_with); mto($$, $1); mto($$, $3); }
        | property_expr "s_until_with" property_expr
                { init($$, ID_sva_s_until_with); mto($$, $1); mto($$, $3); }
        | property_expr "implies" property_expr
                { init($$, ID_sva_implies); mto($$, $1); mto($$, $3); }
        | property_expr "iff" property_expr
                { init($$, ID_sva_iff); mto($$, $1); mto($$, $3); }
        | "accept_on" '(' expression_or_dist ')' property_expr %prec "property_expr_abort"
                { init($$, ID_sva_accept_on); mto($$, $3); mto($$, $5); }
        | "reject_on" '(' expression_or_dist ')' property_expr %prec "property_expr_abort"
                { init($$, ID_sva_reject_on); mto($$, $3); mto($$, $5); }
        | "sync_accept_on" '(' expression_or_dist ')' property_expr %prec "property_expr_abort"
                { init($$, ID_sva_sync_accept_on); mto($$, $3); mto($$, $5); }
        | "sync_reject_on" '(' expression_or_dist ')' property_expr %prec "property_expr_abort"
                { init($$, ID_sva_sync_reject_on); mto($$, $3); mto($$, $5); }
        | clocking_event property_expr { $$=$2; } %prec "property_expr_clocking_event"
        //
        // copy of sequence_expr, to allow and/or to be both sequence_expr and property_expr
        //
        | cycle_delay_range sequence_expr %prec "##"
                { $$=$1;
                  stack_expr($$).operands().insert(stack_expr($$).operands().begin(), nil_exprt());
                  mto($$, $2); }
        // requires sequence_expr on the LHS
        | property_expr cycle_delay_range sequence_expr %prec "##"
                { $$=$2;
                  // preserve the operand ordering as in the source code
                  stack_expr($$).operands().insert(stack_expr($$).operands().begin(), stack_expr($1));
                  mto($$, $3); }
        // requires sequence_expr on the LHS
        | '(' property_expr_proper ')' sequence_abbrev
                { $$ = $4;
                  // preserve the operand ordering as in the source code
                  stack_expr($$).operands().insert(stack_expr($$).operands().begin(), stack_expr($2));
                }
        | expression_or_dist boolean_abbrev
                { $$ = $2;
                  // preserve the operand ordering as in the source code
                  stack_expr($$).operands().insert(stack_expr($$).operands().begin(), stack_expr($1));
                }
        // requires sequence_expr on the LHS
        | property_expr "intersect" sequence_expr
                { init($$, ID_sva_sequence_intersect); mto($$, $1); mto($$, $3); }
        | "first_match" '(' sequence_expr ')'
                { init($$, ID_sva_sequence_first_match); mto($$, $3); stack_expr($$).add_to_operands(nil_exprt{}); }
        | "first_match" '(' sequence_expr ',' sequence_match_item_brace ')'
                { init($$, ID_sva_sequence_first_match); mto($$, $3); mto($$, $5); }
        | expression_or_dist "throughout" sequence_expr
                { init($$, ID_sva_sequence_throughout); mto($$, $1); mto($$, $3); }
        // requires sequence_expr on the LHS
        | property_expr "within" sequence_expr
                { init($$, ID_sva_sequence_within); mto($$, $1); mto($$, $3); }
        ;

property_case_item_brace:
          property_case_item
                { init($$); mto($$, $1); }
        | property_case_item_brace property_case_item
                { $$ = $1; mto($$, $2); }
        ;

property_case_item:
          expression_or_dist_brace TOK_COLON property_expr ';'
                { init($$, ID_case_item); mto($$, $1); mto($$, $3); }
        | "default" TOK_COLON property_expr ';'
                { init($$, ID_case_item); mto($$, $3); }
        ;

sequence_declaration:
          "sequence" { init($$, ID_verilog_sequence_declaration); }
          any_identifier
                { auto base_name = stack_expr($3).get(ID_base_name);
                  push_scope(base_name, ".", verilog_scopet::SEQUENCE);
                }
          sequence_port_list_opt ';'
          sequence_expr semicolon_opt
          "endsequence" sequence_identifier_opt
                { $$=$2;
                  stack_expr($$).set(ID_base_name, stack_expr($3).get(ID_base_name));
                  mto($$, $7);
                  pop_scope();
                }
        ;

sequence_port_list_opt:
          /* Optional */
                { init($$); }
        | '(' ')'
                { init($$); }
        | '(' sequence_port_list ')'
                { $$=$2; }
        ;

sequence_port_list:
          sequence_port_item
                { init($$); mto($$, $1); }
        | sequence_port_list sequence_port_item
                { $$=$1; mto($$, $2); }
        ;

sequence_port_item:
          formal_port_identifier
        ;

sequence_identifier_opt:
          /* Optional */
        | TOK_COLON sequence_identifier
        ;

semicolon_opt:
          /* Optional */
        | ';'
        ;

expression_or_dist_brace:
          expression_or_dist
                { init($$, "patterns"); mto($$, $1); }
        | expression_or_dist_brace ',' expression_or_dist
                { $$ = $1; mto($1, $3); }
        ;

// The 1800-2017 grammar has an ambiguity where
// '(' expression ')' can either be an expression or a sequence_expr,
// which yields a reduce/reduce conflict. Hence, we split the rules
// for sequence_expr into sequence_expr and sequence_expr_proper.

sequence_expr:
          expression_or_dist
        | sequence_expr_proper
        ;

sequence_expr_proper:
          cycle_delay_range sequence_expr %prec "##"
                { $$=$1;
                  stack_expr($$).operands().insert(stack_expr($$).operands().begin(), nil_exprt());
                  mto($$, $2); }
        | sequence_expr cycle_delay_range sequence_expr %prec "##"
                { $$=$2;
                  // preserve the operand ordering as in the source code
                  stack_expr($$).operands().insert(stack_expr($$).operands().begin(), stack_expr($1));
                  mto($$, $3); }
        | '(' sequence_expr_proper ')'
                { $$ = $2; }
        | '(' sequence_expr_proper ')' sequence_abbrev
                { $$ = $4;
                  // preserve the operand ordering as in the source code
                  stack_expr($$).operands().insert(stack_expr($$).operands().begin(), stack_expr($2));
                }
        | expression_or_dist boolean_abbrev
                { $$ = $2;
                  // preserve the operand ordering as in the source code
                  stack_expr($$).operands().insert(stack_expr($$).operands().begin(), stack_expr($1));
                }
        | sequence_expr "and" sequence_expr
                { init($$, ID_sva_and); mto($$, $1); mto($$, $3); }
        | sequence_expr "intersect" sequence_expr
                { init($$, ID_sva_sequence_intersect); mto($$, $1); mto($$, $3); }
        | sequence_expr "or" sequence_expr
                { init($$, ID_sva_or); mto($$, $1); mto($$, $3); }
        | "first_match" '(' sequence_expr ')'
                { init($$, ID_sva_sequence_first_match); mto($$, $3); stack_expr($$).add_to_operands(nil_exprt{}); }
        | "first_match" '(' sequence_expr ',' sequence_match_item_brace ')'
                { init($$, ID_sva_sequence_first_match); mto($$, $3); mto($$, $5); }
        | expression_or_dist "throughout" sequence_expr
                { init($$, ID_sva_sequence_throughout); mto($$, $1); mto($$, $3); }
        | sequence_expr "within" sequence_expr
                { init($$, ID_sva_sequence_within); mto($$, $1); mto($$, $3); }
        ;

sequence_match_item_brace:
          sequence_match_item
        | sequence_match_item_brace ',' sequence_match_item
        ;

sequence_match_item:
          operator_assignment
        | inc_or_dec_expression
        | subroutine_call
        ;

boolean_abbrev:
          consecutive_repetition
        | non_consecutive_repetition
        | goto_repetition
        ;

sequence_abbrev:
          consecutive_repetition
        ;

consecutive_repetition:
          "[*" const_or_range_expression ']'
                { init($$, ID_sva_sequence_repetition_star);
                  if(stack_expr($2).id() == ID_sva_cycle_delay)
                    swapop($$, $2);
                  else
                  {
                    mto($$, $2);
                    stack_expr($$).add_to_operands(nil_exprt{});
                  }
                }
        | "[*" ']'
                { init($$, ID_sva_sequence_repetition_star);
                  stack_expr($$).add_to_operands(nil_exprt{}, nil_exprt{});
                }
        | "[+" ']'
                { init($$, ID_sva_sequence_repetition_plus);
                  stack_expr($$).add_to_operands(nil_exprt{}, nil_exprt{});
                }
        ;

non_consecutive_repetition:
          "[=" const_or_range_expression ']'
                { init($$, ID_sva_sequence_non_consecutive_repetition);
                  if(stack_expr($2).id() == ID_sva_cycle_delay)
                    swapop($$, $2);
                  else
                  {
                    mto($$, $2);
                    stack_expr($$).add_to_operands(nil_exprt{});
                  }
                }
        ;

goto_repetition:
          "[->" const_or_range_expression ']'
                { init($$, ID_sva_sequence_goto_repetition);
                  if(stack_expr($2).id() == ID_sva_cycle_delay)
                    swapop($$, $2);
                  else
                  {
                    mto($$, $2);
                    stack_expr($$).add_to_operands(nil_exprt{});
                  }
                }
        ;

cycle_delay_range:
          "##" number
                { init($$, ID_sva_cycle_delay); mto($$, $2); stack_expr($$).operands().push_back(nil_exprt()); }
        | "##" '[' cycle_delay_const_range_expression ']'
                { $$ = $3; }
        | "##" "[*" ']'
                { init($$, ID_sva_cycle_delay_star); }
        | "##" "[+" ']'
                { init($$, ID_sva_cycle_delay_plus); }
        ;

const_or_range_expression:
          constant_expression
        | cycle_delay_const_range_expression
        ;

cycle_delay_const_range_expression:
          constant_expression TOK_COLON constant_expression
                { init($$, ID_sva_cycle_delay); mto($$, $1); mto($$, $3); }
        | constant_expression TOK_COLON '$'
                { init($$, ID_sva_cycle_delay); mto($$, $1); stack_expr($$).add_to_operands(exprt(ID_infinity)); }
        ;

expression_or_dist:
          expression
        | expression TOK_DIST '{' dist_list '}'
        ;

// System Verilog standard 1800-2017
// A.2.11 Covergroup declarations

covergroup_declaration:
          TOK_COVERGROUP any_identifier tf_port_list_paren_opt coverage_event_opt ';'
          coverage_spec_or_option_brace TOK_ENDGROUP
                { init($$, ID_verilog_covergroup); }
        ;

coverage_spec_or_option_brace:
          /* Optional */
        | coverage_spec_or_option_brace coverage_spec_or_option
        ;

coverage_spec_or_option:
          attribute_instance_brace coverage_spec
        ;

coverage_spec:
          cover_point
        ;

coverage_event_opt:
          /* Optional */
        | coverage_event
        ;

coverage_event:
          clocking_event
        ;

block_event_expression:
          block_event_expression TOK_OR block_event_expression
        | TOK_BEGIN hierarchical_btf_identifier
        | TOK_END hierarchical_btf_identifier
        ;

hierarchical_btf_identifier:
          hierarchical_tf_identifier
        | hierarchical_block_identifier
        | method_identifier
        | hierarchical_identifier '.' method_identifier
        | class_scope method_identifier
        ;

cover_point:
          TOK_COVERPOINT expression ';'
        ;

// System Verilog standard 1800-2017
// A.2.12 Let declarations

let_declaration:
          TOK_LET let_identifier let_port_list_paren_opt '=' expression ';'
                {
                  init($$, ID_verilog_let);
                  // These have one declarator exactly.
                  stack_expr($2).id(ID_declarator);
                  addswap($2, ID_type, $3);
                  addswap($2, ID_value, $5);
                  mto($$, $2);
                }
        ;

let_identifier: identifier;

let_port_list_paren_opt:
          /* Optional */
                { init($$, ID_nil); }
        | '(' let_port_list_opt ')'
                { $$ = $2; }
        ;

let_port_list_opt:
          /* Optional */
                { init($$, ID_nil); }
        | let_port_list
        ;

let_port_list:
          let_port_item
                { init($$); mts($$, $1); }
        | let_port_list ',' let_port_item
                { $$ = $1; mts($$, $3); }
        ;

let_port_item:
          attribute_instance_brace let_formal_type formal_port_identifier
          variable_dimension_brace let_port_initializer_opt
        ;

let_port_initializer_opt:
          /* Optional */
        | '=' expression
        ;

let_formal_type:
          data_type_or_implicit
        | TOK_UNTYPED
                { init($$, ID_verilog_untyped); }
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
//      | pulldown_strength
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
//      | pullup_strength
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
        | TOK_XNOR     { init($$, ID_xnor); }
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
        | gate_instance_brace ',' gate_instance
                { $$=$1;    mto($$, $3); }
        ;

gate_instance:
          name_of_gate_instance_opt '(' list_of_module_connections_opt ')'
                { $$ = $1;
                  swapop($$, $3);
                }
        ;

name_of_gate_instance_opt:
          /* Optional */ 
                { init($$, ID_inst);
                  stack_expr($$).set(ID_base_name, "$_&#ANON" + PARSER.get_next_id()); }
        | name_of_gate_instance
        ;

name_of_gate_instance:
          any_identifier unpacked_dimension_brace
                { init($$, ID_inst);
                  auto base_name = stack_expr($1).get(ID_base_name);
                  stack_expr($$).set(ID_base_name, base_name);
                  PARSER.scopes.add_name(base_name, "", verilog_scopet::MODULE_INSTANCE);
                  if(stack_expr($2).is_not_nil())
                  {
                    auto &range = stack_expr($$).add(ID_range);
                    range = stack_expr($2).find(ID_range);
                    range.id(ID_range);
                  }
                }
        ;

// System Verilog standard 1800-2017
// A.4.1.1 Module instantiation

module_instantiation:
          module_identifier parameter_value_assignment_opt hierarchical_instance_brace ';'
                { init($$, ID_inst);
                  auto base_name = stack_expr($1).get(ID_base_name);
                  stack_expr($$).set(ID_module, base_name);
                  addswap($$, ID_parameter_assignments, $2);
                  swapop($$, $3); }
        ;

parameter_value_assignment_opt:
          /* Optional */
                { make_nil($$); }
        | '#' '(' list_of_parameter_assignments_opt ')'
                { $$ = $3; }
        ;

list_of_parameter_assignments_opt:
          /* Optional */
                { make_nil($$); }
        | list_of_parameter_assignments
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

ordered_parameter_assignment: param_expression
        ;

param_expression:
          expression
        | data_type
                { init($$, ID_type); stack_expr($$).type() = stack_type($1); }
        ;

param_expression_opt:
          /* empty */
                { init($$, ID_nil); }
        | param_expression
        ;

named_parameter_assignment:
          '.' parameter_identifier '(' param_expression_opt ')'
                { init($$, ID_named_parameter_assignment);
                  auto base_name = stack_expr($2).get(ID_base_name);
                  stack_expr($$).set(ID_parameter, base_name);
                  stack_expr($$).add(ID_value).swap(stack_expr($4));
                }
        ;

hierarchical_instance_brace:
          hierarchical_instance
                { init($$); mto($$, $1); }
        | hierarchical_instance_brace ',' hierarchical_instance
                { $$=$1;    mto($$, $3); }
        ;

hierarchical_instance:
          name_of_instance '(' list_of_module_connections_opt ')'
                { $$ = $1; swapop($$, $3); }
        ;

name_of_instance:
                /* Optional */
                { init($$, ID_inst);
                  stack_expr($$).set(ID_base_name, "$_&#ANON" + PARSER.get_next_id());
                }
        | any_identifier unpacked_dimension_brace
                { init($$, ID_inst);
                  auto base_name = stack_expr($1).get(ID_base_name);
                  stack_expr($$).set(ID_base_name, base_name);
                  addswap($$, ID_verilog_instance_array, $2);
                  PARSER.scopes.add_name(base_name, "", verilog_scopet::MODULE_INSTANCE);
                }
        ;

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
          // This needs to be 'any_identifier' to allow identifiers that
          // are typedefs in the local scope.
          '.' any_identifier '(' expression_opt ')'
                { init($$, ID_verilog_named_port_connection);
                  mto($$, $2);
                  mto($$, $4); }
        | ".*" { init($$, ID_verilog_wildcard_port_connection); }
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
          TOK_FOR '(' genvar_initialization ';'
                      genvar_expression ';'
                      genvar_iteration ')'
          generate_block
                { init($$, ID_generate_for);
                  stack_expr($$).reserve_operands(4);
                  mto($$, $3);
                  mto($$, $5);
                  mto($$, $7);
                  mto($$, $9);
                }
        ;

genvar_expression: constant_expression;

genvar_initialization:
          genvar_identifier '=' constant_expression
                { init($$, ID_generate_assign); mto($$, $1); mto($$, $3); }
        | TOK_GENVAR genvar_identifier '=' constant_expression
                { init($$, ID_verilog_generate_decl);
                  PARSER.scopes.add_name(stack_expr($2).get(ID_base_name), "", verilog_scopet::OTHER);
                  stack_expr($2).id(ID_declarator);
                  addswap($2, ID_value, $4);
                  mto($$, $2);
                }
        ;

genvar_iteration:
          genvar_identifier assignment_operator genvar_expression
                { init($$, ID_generate_assign); mto($$, $1); mto($$, $3); }
        | inc_or_dec_operator genvar_identifier
                { $$ = $1; mto($$, $2); }
        | genvar_identifier inc_or_dec_operator
                { $$ = $2; mto($$, $1); }
        ;

conditional_generate_construct:
          if_generate_construct
        | case_generate_construct
        ;

if_generate_construct:
          TOK_IF '(' constant_expression ')' generate_block %prec LT_TOK_ELSE
                { init($$, ID_generate_if); mto($$, $3); mto($$, $5); }
        | TOK_IF '(' constant_expression ')' generate_block TOK_ELSE generate_block
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
          expression_brace TOK_COLON generate_block
        | TOK_DEFAULT TOK_COLON generate_block
        | TOK_DEFAULT generate_block
        ;

generate_block:
          generate_item
        | TOK_BEGIN generate_item_brace TOK_END
                { init($$, ID_generate_block); swapop($$, $2); }
        | TOK_BEGIN TOK_COLON any_identifier
                { push_scope(stack_expr($3).get(ID_base_name), ".", verilog_scopet::BLOCK); }
          generate_item_brace TOK_END
                { pop_scope();
                  init($$, ID_generate_block);
                  swapop($$, $5);
                  stack_expr($$).set(ID_base_name, stack_expr($3).get(ID_base_name));
                }
        ;

generate_item:
          module_or_generate_item
        ;

constant_expression: expression;

// System Verilog standard 1800-2017
// A.5.1 UDP declaration

udp_nonansi_declaration:
          attribute_instance_brace
          TOK_PRIMITIVE udp_identifier '(' udp_port_list ')' ';'
        ;

udp_ansi_declaration:
          attribute_instance_brace
          TOK_PRIMITIVE udp_identifier '(' udp_declaration_port_list ')' ';'
        ;

udp_declaration:
          udp_nonansi_declaration
          udp_port_declaration
          udp_port_declaration_brace
          udp_body
          TOK_ENDPRIMITIVE
        | udp_ansi_declaration
          udp_body
          TOK_ENDPRIMITIVE
        | TOK_EXTERN udp_nonansi_declaration
        | TOK_EXTERN udp_ansi_declaration
        | attribute_instance_brace
          TOK_PRIMITIVE udp_identifier '(' ')' ';'
          udp_port_declaration_brace
          udp_body
          TOK_ENDPRIMITIVE
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

udp_body: combinational_body ;

combinational_body:
          TOK_TABLE
          combinational_entry_brace
          TOK_ENDTABLE
        ;

combinational_entry_brace:
          combinational_entry
        | combinational_entry_brace combinational_entry
        ;

combinational_entry:
          level_input_list TOK_COLON output_symbol ';'
        ;

sequential_body:
          udp_initial_statement_opt
          TOK_TABLE sequential_entry_brace TOK_ENDTABLE
        ;

udp_initial_statement_opt:
          /* Optional */
        | udp_initial_statement
        ;

udp_initial_statement:
          TOK_INITIAL output_port_identifier '=' init_val ';'
        ;

output_port_identifier: any_identifier
        ;

init_val:
        // Really 1'b0 | 1'b1 | 1'bx | 1'bX | 1'B0 | 1'B1 | 1'Bx | 1'BX | 1 | 0
          TOK_NUMBER
        | any_identifier
        ;

sequential_entry_brace:
          sequential_entry
        | sequential_entry_brace sequential_entry
        ;

sequential_entry:
          seq_input_list TOK_COLON current_state TOK_COLON next_state
        ;

seq_input_list: level_input_list | edge_input_list
        ;

edge_indicator:
          '(' level_symbol level_symbol ')' | edge_symbol
        ;

current_state: level_symbol ;

next_state: output_symbol | '-' ;

level_input_list:
          level_symbol
        | level_input_list level_symbol
        ;

edge_input_list: level_symbol_brace edge_indicator level_symbol_brace ;

output_symbol:
        // Really 0 | 1 | x | X
          TOK_NUMBER
        | any_identifier
        ;

level_symbol_brace:
          level_symbol
        | level_symbol_brace level_symbol
        ;

level_symbol:
        // Really 0 | 1 | x | X | ? | b | B
          TOK_NUMBER
        | any_identifier
        ;

edge_symbol:
        // Really r | R | f | F | p | P | n | N | *
          TOK_NUMBER
        | any_identifier
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

list_of_variable_assignments:
          variable_assignment
                { init($$); mto($$, $1); }
        | list_of_variable_assignments ',' variable_assignment
                { $$=$1;    mto($$, $3); }
        ;

net_assignment: net_lvalue '=' expression
                { init($$, ID_equal); mto($$, $1); mto($$, $3); }
        ;

// System Verilog standard 1800-2017
// A.6.2 Procedural blocks and assignments

initial_construct: TOK_INITIAL statement_or_null
                { init($$, ID_initial); mto($$, $2); }
        ;

always_construct: always_keyword statement
                { $$=$1; mto($$, $2); }
        ;

always_keyword:
          TOK_ALWAYS       { init($$, ID_verilog_always); }
        | TOK_ALWAYS_COMB  { init($$, ID_verilog_always_comb); }
        | TOK_ALWAYS_LATCH { init($$, ID_verilog_always_latch); }
        | TOK_ALWAYS_FF    { init($$, ID_verilog_always_ff); }
        ;

final_construct: TOK_FINAL function_statement
                { init($$, ID_verilog_final); mto($$, $2); }
        ;

blocking_assignment:
          variable_lvalue '=' delay_or_event_control expression
                { init($$, ID_verilog_blocking_assign); mto($$, $1); mto($$, $4); }
        | operator_assignment
        ;

operator_assignment:
          variable_lvalue assignment_operator expression
                { $$ = $2; mto($$, $1); mto($$, $3); }
        ;

assignment_operator:
          '='
                { init($$, ID_verilog_blocking_assign); }
        | TOK_PLUSEQUAL
                { init($$, ID_verilog_blocking_assign_plus); }
        | TOK_MINUSEQUAL
                { init($$, ID_verilog_blocking_assign_minus); }
        | TOK_ASTERICEQUAL
                { init($$, ID_verilog_blocking_assign_mult); }
        | TOK_SLASHEQUAL
                { init($$, ID_verilog_blocking_assign_div); }
        | TOK_PERCENTEQUAL
                { init($$, ID_verilog_blocking_assign_mod); }
        | TOK_AMPEREQUAL
                { init($$, ID_verilog_blocking_assign_bitand); }
        | TOK_VERTBAREQUAL
                { init($$, ID_verilog_blocking_assign_bitor); }
        | TOK_CARETEQUAL
                { init($$, ID_verilog_blocking_assign_bitxor); }
        | TOK_LESSLESSEQUAL
                { init($$, ID_verilog_blocking_assign_lshl); }
        | TOK_GREATERGREATEREQUAL
                { init($$, ID_verilog_blocking_assign_lshr); }
        | TOK_LESSLESSLESSEQUAL
                { init($$, ID_verilog_blocking_assign_ashl); }
        | TOK_GREATERGREATERGREATEREQUAL
                { init($$, ID_verilog_blocking_assign_ashr); }
        ;

nonblocking_assignment:
          variable_lvalue TOK_LESSEQUAL expression
                { init($$, ID_verilog_non_blocking_assign); mto($$, $1); mto($$, $3); }
        | variable_lvalue TOK_LESSEQUAL delay_or_event_control expression
                { init($$, ID_verilog_non_blocking_assign); mto($$, $1); mto($$, $4); }
        ;

procedural_continuous_assignment:
          TOK_ASSIGN variable_assignment
                { init($$, ID_procedural_continuous_assign); mto($$, $2); }
        | TOK_DEASSIGN variable_lvalue
                { init($$, ID_deassign); mto($$, $2); }
        | TOK_FORCE variable_assignment
                { init($$, ID_force); swapop($$, $2); }
        /* | TOK_FORCE net_assignment */
        | TOK_RELEASE variable_lvalue
                { init($$, ID_release); mto($$, $2); }
        /* | TOK_RELEASE net_lvalue */
        ;

variable_assignment: net_assignment;

subroutine_call_statement:
          subroutine_call ';'
                { $$=$1; }
        ;

// System Verilog standard 1800-2017
// A.6.3 Parallel and sequential blocks

action_block:
          statement_or_null %prec LT_TOK_ELSE
                { init($$, ID_verilog_action_then); mto($$, $1); }
        | TOK_ELSE statement
                { init($$, ID_verilog_action_else); mto($$, $2); }
        | statement_or_null TOK_ELSE statement 
                { init($$, ID_verilog_action_then_else); mto2($$, $1, $3); }
        ;

// The 1800-2017 grammar specifies this to be
// "begin" { block_item_declartion} { statement_or_null } "end".
// This yields ambiguity owing to the
// attribute_instance_brace in block_item_declaration and in
// statement. Instead, we introduce the
// block_item_declaration_or_statement_or_null_brace
// rule to accept both block_item_declaration and statement_or_null.
seq_block:
          TOK_BEGIN
          block_item_declaration_or_statement_or_null_brace
          TOK_END
                { init($$, ID_block); swapop($$, $2); }
        | TOK_BEGIN TOK_COLON any_identifier
                { push_scope(stack_expr($3).get(ID_base_name), ".", verilog_scopet::BLOCK); }
          block_item_declaration_or_statement_or_null_brace
          TOK_END
                { init($$, ID_block);
                  swapop($$, $5);
                  stack_expr($$).set(ID_base_name, stack_expr($3).get(ID_base_name));
                  pop_scope();
                }
        ;

par_block:
          TOK_FORK statement_or_null_brace TOK_JOIN
                { init($$, ID_fork); swapop($$, $2); }
        | TOK_FORK TOK_COLON any_identifier
          statement_or_null_brace TOK_JOIN
                { init($$, ID_block);
                  swapop($$, $4);
                  stack_expr($$).set(ID_base_name, stack_expr($3).get(ID_base_name));
                }
        ;

// System Verilog standard 1800-2017
// A.6.4 Statements

// The next two rules are an addition for the benefit of seq_block,
// to avoid the reduce/reduce conflict on the attribute_instance_brace
// when transitioning between { block_item_declaration }
// and { statement_or_null }. We allow them to interleave arbitrarily.
block_item_declaration_or_statement_or_null_brace:
                /* Optional */
                { init($$); }
        | block_item_declaration_or_statement_or_null_brace
          block_item_declaration_or_statement_or_null
                { $$=$1; mto($$, $2); }
        ;

block_item_declaration_or_statement_or_null:
          block_item_declaration
        | statement_or_null
        ;

statement_or_null:
          statement
        | attribute_instance_brace ';'
                { init($$, ID_skip);
                  add_attributes($$, $1); }
        ;

statement_or_null_brace:
                /* Optional */
                { init($$); }
        | statement_or_null_brace statement_or_null
                { $$=$1; mto($$, $2); }
        ;

// The rule in 1800-2017 does not have the attribute_instance_brace before
// the label. We allow this to avoid a shift/reduce conflict.
statement: 
          attribute_instance_brace block_identifier TOK_COLON attribute_instance_brace statement_item
                { init($$, ID_verilog_label_statement);
                  auto base_name = stack_expr($2).get(ID_base_name);
                  stack_expr($$).set(ID_base_name, base_name);

                  // We'll stick the label onto any assertion
                  auto statement = stack_expr($5).id();
                  if(statement == ID_verilog_immediate_assert ||
                     statement == ID_verilog_immediate_assume ||
                     statement == ID_verilog_immediate_cover)
                  {
                    stack_expr($5).set(ID_base_name, base_name);
                  }

                  mto($$, $5);
                }
        | attribute_instance_brace statement_item
                { $$=$2; }
        ;

statement_item:
          blocking_assignment ';' { $$ = $1; }
        | nonblocking_assignment ';' { $$ = $1; }
        | case_statement
        | conditional_statement
        | inc_or_dec_expression ';'
        | subroutine_call_statement
        | disable_statement
        | event_trigger
        | loop_statement
        | jump_statement
        | par_block
        | procedural_timing_control_statement
        | procedural_continuous_assignment ';'
        | seq_block
        | wait_statement
        | procedural_assertion_statement
        | expect_property_statement
        ;

function_statement: statement
        ;

function_statement_or_null:
          function_statement
        | attribute_instance_brace ';'
                { init($$, ID_skip);
                  add_attributes($$, $1); }
        ;

function_statement_or_null_brace:
          function_statement_or_null
                { init($$); mto($$, $1); }
        | function_statement_or_null_brace function_statement_or_null
                { $$ = $1; mto($$, $2); }
        ;

function_statement_brace:
          /* optional */
        | function_statement_brace function_statement
        ;

system_task_name: TOK_SYSIDENT
                { new_identifier($$, $1); }
        ;

// System Verilog standard 1800-2017
// A.6.5 Timing control statements

delay_or_event_control:
          delay_control
        | event_control
        | TOK_REPEAT '(' expression ')' event_control
                { init($$, ID_repeat); }
        ;


delay_control_opt:
          /* Optional */
        | delay_control
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
                { init($$, ID_verilog_event); mto($$, $1); }
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

jump_statement:
          "return" ';'
                { init($$, ID_return); }
        | "return" expression ';'
                { init($$, ID_return); mto($$, $2); }
        | "break" ';'
                { init($$, ID_break); }
        | "continue" ';'
                { init($$, ID_continue); }
        ;

disable_statement: TOK_DISABLE hierarchical_task_or_block_identifier ';'
                { init($$, ID_disable); mto($$, $2); }
        ;

// System Verilog standard 1800-2017
// A.6.6 Conditional statements

conditional_statement:
          unique_priority_opt TOK_IF '(' expression ')' statement_or_null %prec LT_TOK_ELSE
                { init($$, ID_if); mto($$, $4); mto($$, $6); }
        | unique_priority_opt TOK_IF '(' expression ')' statement_or_null TOK_ELSE statement_or_null
                { init($$, ID_if); mto($$, $4); mto($$, $6); mto($$, $8); }
        ;

unique_priority_opt:
          /* Optional */
                { init($$); }
        | TOK_UNIQUE
                { init($$, ID_verilog_unique); }
        | TOK_UNIQUE0
                { init($$, ID_verilog_unique0); }
        | TOK_PRIORITY
                { init($$, ID_verilog_priority); }
        ;

// System Verilog standard 1800-2017
// A.6.7 Case statements

case_statement:
          unique_priority_opt TOK_CASE '(' expression ')' case_item_brace TOK_ENDCASE
                { init($$, ID_case);  mto($$, $4);
                  Forall_operands(it, stack_expr($6))
                    stack_expr($$).add_to_operands(std::move(*it)); }
        | unique_priority_opt TOK_CASEX '(' expression ')' case_item_brace TOK_ENDCASE
                { init($$, ID_casex); mto($$, $4);
                  Forall_operands(it, stack_expr($6))
                    stack_expr($$).add_to_operands(std::move(*it)); }
        | unique_priority_opt TOK_CASEZ '(' expression ')' case_item_brace TOK_ENDCASE
                { init($$, ID_casez); mto($$, $4);
                  Forall_operands(it, stack_expr($6))
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

open_range_list:
          open_value_range
                { init($$); mto($$, $1); }
        | open_range_list ',' open_value_range
                { $$=$1; mto($$, $3); }
        ;

open_value_range: value_range;

// System Verilog standard 1800-2017
// A.6.7.1 Patterns

pattern:
          "." variable_identifier
        | ".*"
        | constant_expression
        | "tagged" member_identifier
        | "tagged" member_identifier pattern
        | "'{" pattern_list "}"
        | "'{" member_pattern_list "}"
        ;

pattern_list:
          pattern
        | pattern_list "," pattern
        ;

member_pattern_list:
          member_identifier ":" pattern
        | member_pattern_list "," member_identifier ":" pattern
        ;

assignment_pattern:
          '\'' '{' expression_brace '}'
                { init($$, ID_verilog_assignment_pattern); swapop($$, $3); }
        | '\'' '{' structure_pattern_key_brace '}'
                { init($$, ID_verilog_assignment_pattern); swapop($$, $3); }
        ;

structure_pattern_key_and_expression:
          structure_pattern_key TOK_COLON expression
                { $$ = $1; mto($$, $3); }
        ;

structure_pattern_key_brace:
          structure_pattern_key_and_expression
                { init($$); mto($$, $1); }
        | structure_pattern_key_brace ',' structure_pattern_key_and_expression
                { $$ = $1; mto($$, $3); }
        ;

structure_pattern_key:
          member_identifier
                {
                  init($$, ID_member_initializer);
                  stack_expr($$).set(ID_member_name, stack_expr($1).get(ID_base_name));
                }
        ;

assignment_pattern_expression:
          assignment_pattern
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

for_initialization:
          list_of_variable_assignments
                { // Turn the variable_assignments into statements
                  // by changing the id to ID_verilog_blocking_assign
                  auto &assignments = stack_expr($1).operands();
                  for(auto &assignment : assignments)
                    assignment.id(ID_verilog_blocking_assign);
                }
        | for_variable_declaration_brace
        ;

for_variable_declaration_brace:
          for_variable_declaration
                { init($$); mto($$, $1); }
        | for_variable_declaration_brace ',' for_variable_declaration
                { $$ = $1; mto($$, $3); }
        ;

for_variable_declaration:
          data_type variable_identifier '=' expression
                { // these create a scope -- unlike for loops without declaration
                  init($$, ID_decl);
                  stack_expr($$).set(ID_class, ID_var);
                  addswap($$, ID_type, $1);
                  stack_expr($2).id(ID_declarator);
                  addswap($2, ID_value, $4);
                  mto($$, $2);
                }
        | TOK_VAR data_type variable_identifier '=' expression
                { // these create a scope -- unlike for loops without declaration
                  init($$, ID_decl);
                  stack_expr($$).set(ID_class, ID_var);
                  addswap($$, ID_type, $2);
                  stack_expr($3).id(ID_declarator);
                  addswap($3, ID_value, $5);
                  mto($$, $3);
                }
        ;

for_step: for_step_assignment
        ;

for_step_assignment:
          operator_assignment
        | inc_or_dec_expression
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

assertion_item:
          concurrent_assertion_item
        | deferred_immediate_assertion_item
        ;

deferred_immediate_assertion_item:
          deferred_immediate_assertion_statement
                { /* wrap the statement into an item */
                  init($$, ID_verilog_assertion_item);
                  mto($$, $1);
                }
        | block_identifier TOK_COLON deferred_immediate_assertion_statement
                { /* wrap the statement into an item */
                  auto base_name = stack_expr($1).get(ID_base_name);
                  stack_expr($3).set(ID_base_name, base_name);
                  init($$, ID_verilog_assertion_item);
                  mto($$, $3);
                }
        ;

procedural_assertion_statement:
          concurrent_assertion_statement
        | immediate_assertion_statement
        /* | checker_instantiation */
        | smv_assertion_statement
        ;

immediate_assertion_statement:
          simple_immediate_assertion_statement
        | deferred_immediate_assertion_statement
        ;

simple_immediate_assertion_statement:
          simple_immediate_assert_statement
        | simple_immediate_assume_statement
        | simple_immediate_cover_statement
        ;

simple_immediate_assert_statement: TOK_ASSERT '(' expression ')' action_block
                { init($$, ID_verilog_immediate_assert); mto($$, $3); mto($$, $5); }
        ;

simple_immediate_assume_statement: TOK_ASSUME '(' expression ')' action_block
                { init($$, ID_verilog_immediate_assume); mto($$, $3); mto($$, $5); }
        ;

simple_immediate_cover_statement: TOK_COVER '(' expression ')' action_block
                { init($$, ID_verilog_immediate_cover); mto($$, $3); mto($$, $5); }
        ;

deferred_immediate_assertion_statement:
          deferred_immediate_assert_statement
        | deferred_immediate_assume_statement
        | deferred_immediate_cover_statement
        ;

deferred_immediate_assert_statement:
          TOK_ASSERT TOK_FINAL '(' expression ')' action_block
                { init($$, ID_verilog_immediate_assert); mto($$, $4); mto($$, $6); }
        ;

deferred_immediate_assume_statement:
          TOK_ASSUME TOK_FINAL '(' expression ')' action_block
                { init($$, ID_verilog_immediate_assume); mto($$, $4); mto($$, $6); }
        ;

deferred_immediate_cover_statement:
          TOK_COVER TOK_FINAL '(' expression ')' statement_or_null
                { init($$, ID_verilog_immediate_cover); mto($$, $4); mto($$, $6); }
        ;

wait_statement: TOK_WAIT '(' expression ')' statement_or_null
                { init($$, ID_wait); mto($$, $3); mto($$, $5); }
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

clocking_declaration:
          TOK_DEFAULT TOK_CLOCKING clocking_identifier_opt clocking_event ';'
          clocking_item_brace
          TOK_ENDCLOCKING
                { init($$, ID_verilog_clocking); }
        | TOK_CLOCKING clocking_identifier_opt clocking_event ';'
          clocking_item_brace
          TOK_ENDCLOCKING
                { init($$, ID_verilog_clocking); }
        | TOK_GLOBAL TOK_CLOCKING clocking_identifier_opt clocking_event ';'
          TOK_ENDCLOCKING
                { init($$, ID_verilog_clocking); }
        ;

clocking_identifier_opt:
          /* Optional */
        | clocking_identifier
        ;

clocking_event:
          '@' identifier
        | '@' '(' event_expression ')'
        ;

clocking_item_brace:
          /* Optional */
        | clocking_item_brace clocking_item
        ;

clocking_item:
          TOK_DEFAULT default_skew ';'
        | attribute_instance_brace assertion_item_declaration
        ;

default_skew:
          TOK_INPUT clocking_skew
        | TOK_OUTPUT clocking_skew
        | TOK_INPUT clocking_skew TOK_OUTPUT clocking_skew
        ;

clocking_direction:
          TOK_INPUT clocking_skew_opt
        | TOK_OUTPUT clocking_skew_opt
        | TOK_INPUT clocking_skew_opt TOK_OUTPUT clocking_skew_opt
        | TOK_INOUT
        ;

list_of_clocking_decl_assign:
          clocking_decl_assign
        | list_of_clocking_decl_assign ',' clocking_decl_assign
        ;

clocking_decl_assign:
          signal_identifier
        | signal_identifier '=' expression
        ;

clocking_skew_opt:
          /* Optional */
        | clocking_skew
        ;

clocking_skew:
          edge_identifier delay_control_opt
        | delay_control
        ;

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

multiple_concatenation:
          '{' expression concatenation '}'
                { init($$, ID_replication); mto($$, $2); mto($$, $3); }
        | '{' expression multiple_concatenation '}'
                { init($$, ID_replication); mto($$, $2); mto($$, $3); }
        ;

streaming_concatenation:
          '{' stream_operator stream_concatenation '}'
                { $$ = $2; mto($$, $3); }
        | '{' stream_operator slice_size stream_concatenation '}'
                { $$ = $2; mto($$, $3); mto($$, $4); }
        ;

stream_operator:
          TOK_GREATERGREATER
                { init($$, ID_verilog_streaming_concatenation_left_to_right); }
        | TOK_LESSLESS
                { init($$, ID_verilog_streaming_concatenation_right_to_left); }
        ;

slice_size:
          simple_type
        | primary_literal /* really constant_expression */
        ;

stream_concatenation:
          '{' stream_expression_brace '}'
                { $$ = $2; }
        ;

stream_expression_brace:
          stream_expression
                { init($$); mto($$, $1); }
        | stream_expression_brace ',' stream_expression
                { $$ = $1; mto($$, $3); }
        ;

stream_expression:
          expression
        | expression TOK_WITH '[' array_range_expression ']'
                { init($$, ID_verilog_array_range); mto($$, $1); mto($$, $4); }
        ;

array_range_expression:
          expression
        | expression TOK_COLON expression
        | expression TOK_PLUSCOLON expression
        | expression TOK_MINUSCOLON expression
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
          hierarchical_identifier list_of_arguments_paren_opt
                { init($$, ID_function_call);
                  stack_expr($$).operands().reserve(2);
                  mto($$, $1); mto($$, $2); }
        ;

list_of_arguments_paren:
          '(' list_of_arguments ')'
                { $$ = $2; }
        ;

list_of_arguments_paren_opt:
          /* Optional */
                { init($$); }
        | list_of_arguments_paren
        ;

list_of_arguments:
          /* Optional */
                { init($$); }
        | expression
                { init($$); mto($$, $1); }
        | list_of_arguments ',' expression
                { $$=$1;    mto($$, $3); }
        ;

system_tf_call:
          system_task_name
                { init($$, ID_function_call);
                  stack_expr($$).operands().resize(2);
                  stack_expr($$).operands()[0].swap(stack_expr($1)); }
        | system_task_name '(' list_of_arguments ')'
                { init($$, ID_function_call);
                  stack_expr($$).operands().reserve(2);
                  mto($$, $1); mto($$, $3); }
        | system_task_name '(' data_type ')'
                { init($$, ID_function_call);
                  stack_expr($$).operands().reserve(2);
                  mto($$, $1);
                  unary_exprt arguments(ID_arguments, exprt(ID_type, stack_type($3)));
                  stack_expr($$).add_to_operands(arguments); }
        ;

subroutine_call:
          tf_call
        | system_tf_call
        ;

// We deviate from the 1800-2017 grammar to remove the ambiguity
// between function calls without parentheses and variables.
// Note that this does not affect system function identifiers ($...),
// which cannot be variables.
function_subroutine_call:
          hierarchical_tf_identifier list_of_arguments_paren
                { init($$, ID_function_call);
                  stack_expr($$).operands().reserve(2);
                  mto($$, $1); mto($$, $2); }
        | system_tf_call
        ;

event_trigger: TOK_MINUSGREATER hierarchical_event_identifier ';'
                { init($$, ID_verilog_event_trigger); mto($$, $2); }
        ;

// System Verilog standard 1800-2017
// A.8.3 Expressions

inc_or_dec_expression:
          TOK_PLUSPLUS attribute_instance_brace variable_lvalue
                { init($$, ID_preincrement); mto($$, $3); add_attributes($$, $2); }
        | TOK_MINUSMINUS attribute_instance_brace variable_lvalue
                { init($$, ID_predecrement); mto($$, $3); add_attributes($$, $2); }
        | variable_lvalue attribute_instance_brace TOK_PLUSPLUS
                { init($$, ID_postincrement); mto($$, $1); add_attributes($$, $2); }
        | variable_lvalue attribute_instance_brace TOK_MINUSMINUS
                { init($$, ID_postdecrement); mto($$, $1); add_attributes($$, $2); }
        ;

constant_param_expression:
          constant_expression
        | '$'
                { init($$, ID_infinity); }
        ;

constant_range:
          const_expression TOK_COLON const_expression
                { init($$, ID_verilog_non_indexed_part_select); mto($$, $1); mto($$, $3); }
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
                { $$=$1; mto($$, $3); add_attributes($$, $2); }
        | inc_or_dec_expression
        | expression "->" expression
                { init($$, ID_verilog_implies); mto($$, $1); mto($$, $3); }
        | expression "<->" expression
                { init($$, ID_verilog_iff); mto($$, $1); mto($$, $3); }
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
                { init($$, ID_verilog_logical_equality); mto($$, $1); mto($$, $3); }
        | expression TOK_EXCLAMEQUAL expression
                { init($$, ID_verilog_logical_inequality); mto($$, $1); mto($$, $3); }
        | expression TOK_EQUALEQUALQUESTION expression
                { init($$, ID_verilog_wildcard_equality); mto($$, $1); mto($$, $3); }
        | expression TOK_EXCLAMEQUALQUESTION expression
                { init($$, ID_verilog_wildcard_inequality); mto($$, $1); mto($$, $3); }
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
        | expression TOK_CARETTILDE expression
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
        | inside_expression
        | tagged_union_expression
        ;

tagged_union_expression:
          TOK_TAGGED member_identifier
                { init($$, ID_verilog_tagged_union); mto($$, $2); }
        ;

inside_expression:
          expression TOK_INSIDE '{' open_range_list '}'
                { init($$, ID_verilog_inside); mto($$, $1); mto($$, $4); }
        ;

value_range:
          expression
        | '[' expression TOK_COLON expression ']'
                { init($$, ID_verilog_value_range); mto($$, $2); mto($$, $4); }
        ;

indexed_range:
          expression TOK_PLUSCOLON constant_expression
                { init($$, ID_verilog_indexed_part_select_plus); mto($$, $1); mto($$, $3); }
        | expression TOK_MINUSCOLON constant_expression
                { init($$, ID_verilog_indexed_part_select_minus); mto($$, $1); mto($$, $3); }
        ;

part_select_range:
          constant_range
        | indexed_range
        ;

// System Verilog standard 1800-2017
// A.8.4 Primaries

primary:  primary_literal
        | hierarchical_identifier_select
        | package_scope hierarchical_identifier_select
                { $$ = $1;
                  mto($$, $2);
                  // exit the package scope
                  pop_scope();
                }
        | concatenation 
        | multiple_concatenation
        | function_subroutine_call
        | '(' mintypmax_expression ')'
                { $$ = $2; }
        | cast
        | assignment_pattern_expression
        | streaming_concatenation
        | TOK_NULL { init($$, ID_verilog_null); }
        | TOK_THIS { init($$, ID_this); }
        ;

primary_literal:
          number
        | time_literal
        ;

constant_primary: primary
        ;

// This is equivalent to two System Verilog 1800-2017 productions
// hierarchical_identifier select.
hierarchical_identifier_select:
          hierarchical_identifier_bit_select_brace
        | hierarchical_identifier_bit_select_brace '[' part_select_range ']'
                { // part_select_range has two operands.
                  // We form a new expression with three operands from it.
                  auto &part_select = to_binary_expr(stack_expr($3));
                  stack_expr($3).operands() =
                    { stack_expr($1), part_select.op0(), part_select.op1() };
                  $$ = $3;
                }
        ;

hierarchical_identifier_bit_select_brace:
          hierarchical_variable_identifier
        | hierarchical_identifier_bit_select_brace constant_bit_select
                { init($$, ID_verilog_bit_select);
                  mto($$, $1);
                  mto($$, $2); }
        ;

time_literal: TOK_TIME_LITERAL
                { init($$, ID_constant);
                  addswap($$, ID_value, $1);
                  stack_expr($$).type().id(ID_verilog_realtime); }
        ;

cast:
          casting_type '\'' '(' expression ')'
                { $$ = $1; mto($$, $4); }
        ;

constant_bit_select:
          '[' constant_expression ']'
                { $$ = $2; }
        ;

constant_select: constant_bit_select;

// System Verilog standard 1800-2017
// A.8.5 Expression left-side values

net_lvalue: variable_lvalue;

variable_lvalue:
          hierarchical_identifier_select
        | concatenation
          /* more generous than the rule below to avoid conflict */
        /*
        | '{' variable_concatenation_lvalue_brace '}'
                { init($$, ID_concatenation); swapop($$, $2); }
        */
        | assignment_pattern
        ;
        
variable_concatenation_lvalue_brace:
          variable_lvalue
                { init($$); mto($$, $1); }
        | variable_concatenation_lvalue_brace ',' variable_lvalue
                { $$=$1;    mto($$, $3); }
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

inc_or_dec_operator:
          TOK_PLUSPLUS     { init($$, ID_preincrement); }
        | TOK_MINUSMINUS   { init($$, ID_predecrement); }
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
                { init($$, ID_verilog_attributes); }
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
                { init($$, ID_verilog_attribute);
                  stack_expr($$).add(ID_name).swap(stack_expr($1));
                  stack_expr($$).add(ID_value).swap(stack_expr($3));
                }
        | attr_name
                { init($$, ID_verilog_attribute); stack_expr($$).add(ID_name).swap(stack_expr($1)); }
        ;

attr_name: identifier
        ;

// System Verilog standard 1800-2017
// A.9.3 Identifiers

// An extension of the System Verilog grammar to allow defining new identifiers
// even if they are already used for a different kind of identifier
// in a higher scope.
any_identifier:
          TOK_TYPE_IDENTIFIER
                { new_identifier($$, $1); }
        | non_type_identifier
        ;

non_type_identifier: TOK_NON_TYPE_IDENTIFIER
                { new_identifier($$, $1); }
        ;

block_identifier: non_type_identifier;

cell_identifier: non_type_identifier;

class_identifier: TOK_CLASS_IDENTIFIER
                {
                  init($$, ID_verilog_class_type);
                  auto base_name = stack_expr($1).id();
                  stack_expr($$).set(ID_base_name, base_name);
                  stack_expr($$).set(ID_verilog_scope_prefix, PARSER.scopes.current_scope().prefix);
                }
        ;

config_identifier: non_type_identifier;

constraint_identifier: non_type_identifier;

edge_identifier: identifier;

formal_port_identifier: identifier;

genvar_identifier: identifier;

hierarchical_parameter_identifier: hierarchical_identifier
        ;

instance_identifier: non_type_identifier;

interface_identifier: non_type_identifier;

module_identifier: non_type_identifier;

topmodule_identifier: non_type_identifier;

endmodule_identifier_opt:
          /* Optional */
        | TOK_COLON module_identifier
        ;

clocking_identifier: non_type_identifier;

checker_identifier: non_type_identifier;

net_identifier: identifier;

package_identifier: TOK_PACKAGE_IDENTIFIER;

package_scope: package_identifier "::"
                {
                  init($$, ID_verilog_package_scope);
                  // enter that scope
                  auto base_name = stack_expr($1).id();
                  PARSER.scopes.enter_package_scope(base_name);
                  mto($$, $1);
                }
        ;

param_identifier: non_type_identifier;

port_identifier: identifier;

ps_covergroup_identifier:
        ;
        
library_identifier: non_type_identifier;

memory_identifier: identifier;

member_identifier: identifier;

method_identifier: identifier;

signal_identifier: identifier;

type_identifier: TOK_TYPE_IDENTIFIER
                {
                  init($$, ID_typedef_type);
                  auto base_name = stack_expr($1).id();
                  stack_expr($$).set(ID_base_name, base_name);
                }
        ;

ps_type_identifier: type_identifier;

parameter_identifier: non_type_identifier;

udp_identifier: non_type_identifier;

task_identifier: hierarchical_identifier
        ;

event_identifier: identifier;

hierarchical_task_or_block_identifier: task_identifier;

hierarchical_tf_identifier: hierarchical_identifier;

specparam_identifier: TOK_NON_TYPE_IDENTIFIER;

function_identifier: hierarchical_identifier
        ;

hierarchical_event_identifier: event_identifier;

hierarchical_block_identifier: hierarchical_identifier;

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

net_type_identifier: TOK_TYPE_IDENTIFIER;

identifier: non_type_identifier;

property_identifier: non_type_identifier;

sequence_identifier: non_type_identifier;

variable_identifier: identifier;

%%
