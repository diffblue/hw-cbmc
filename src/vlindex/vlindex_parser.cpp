/*******************************************************************\

Module: Verilog Indexer Parser

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#include "vlindex_parser.h"

#include <iostream>

verilog_indexer_parsert::tokent verilog_indexer_parsert::next_token()
{
  peek();
  CHECK_RETURN(!tokens.empty());
  auto token = std::move(tokens.front());
  tokens.pop_front();
  return token;
}

// scanner interface
int yyveriloglex();
extern char *yyverilogtext;
extern int yyverilogleng;

verilog_indexer_parsert::tokent verilog_indexer_parsert::fetch_token()
{
  tokent result;
  result.kind = yyveriloglex();
  result.text = std::string(yyverilogtext, yyverilogleng);
  return result;
}

const verilog_indexer_parsert::tokent &
verilog_indexer_parsert::peek(std::size_t k)
{
  PRECONDITION(k >= 1);

  while(tokens.size() < k)
    tokens.push_back(fetch_token());

  // std::deque guarantees that the references remain stable even when adding
  // more tokens.
  return tokens[k - 1];
}

void verilog_indexer_parsert::rDescription()
{
  if(peek().is_eof())
    return; // empty file

  if(next_token().kind != TOK_PARSE_LANGUAGE)
    DATA_INVARIANT(false, "expected TOK_PARSE_LANGUAGE");

  while(!peek().is_eof())
  {
    rItem();
  }
}

/// Covers the various 'definition-like' constructs in SystemVerilog, i.e.,
/// modules, interfaces, classes, primitives, packages, configurations,
/// checkers
void verilog_indexer_parsert::rModule(
  verilog_indexert::idt::kindt kind,
  int end_token)
{
  auto keyword = next_token(); // module, ...

  auto name = next_token();
  if(!name.is_identifier())
    return; // give up

  current_module = name.text;

  idt id;
  id.kind = kind;
  id.name = current_module;
  id.module = current_module;
  id.file_name = verilog_parser.get_file();
  id.line_number = verilog_parser.get_line_no();
  indexer.add(std::move(id));

  if(peek() == TOK_IMPORT)
    rImport();

  if(peek() == TOK_EXTENDS)
    rExtends();

  rPorts();

  // now look for the 'endmodule', given as end_token
  while(!peek().is_eof())
  {
    if(peek() == end_token)
    {
      next_token();
      break; // done with the module
    }
    else
      rItem();
  }

  // optional : name
  if(peek() == TOK_COLON)
  {
    next_token(); // :
    next_token(); // identifier
  }

  current_module = irep_idt();
}

void verilog_indexer_parsert::rItem()
{
  auto &token = peek();

  if(token == TOK_MODULE)
    rModule(verilog_indexert::idt::MODULE, TOK_ENDMODULE);
  else if(token == TOK_CLASS)
    rModule(verilog_indexert::idt::CLASS, TOK_ENDCLASS);
  else if(token == TOK_PRIMITIVE)
    rModule(verilog_indexert::idt::UDP, TOK_ENDPRIMITIVE);
  else if(token == TOK_INTERFACE)
    rModule(verilog_indexert::idt::INTERFACE, TOK_ENDINTERFACE);
  else if(token == TOK_PACKAGE)
    rModule(verilog_indexert::idt::PACKAGE, TOK_ENDPACKAGE);
  else if(token == TOK_CHECKER)
    rModule(verilog_indexert::idt::CHECKER, TOK_ENDCHECKER);
  else if(token == TOK_CONFIG)
    rModule(verilog_indexert::idt::CONFIG, TOK_CONFIG);
  else if(token == TOK_PROPERTY)
    rProperty();
  else if(token == TOK_SEQUENCE)
    rSequence();
  else if(token == TOK_SPECIFY)
    rSpecify();
  else if(token == TOK_MODPORT)
    rModport();
  else if(token == TOK_BIND)
    rBind();
  else if(token == TOK_CELL)
    rCell();
  else if(token == TOK_DESIGN)
    rDesign();
  else if(token == TOK_INTERCONNECT)
    rInterconnect();
  else if(
    token == TOK_ALWAYS || token == TOK_ALWAYS_FF || token == TOK_ALWAYS_COMB ||
    token == TOK_ALWAYS_LATCH || token == TOK_FINAL || token == TOK_INITIAL)
  {
    rConstruct();
  }
  else if(token == TOK_DEFAULT)
  {
    if(peek(2) == TOK_CLOCKING)
      rClocking();
    else if(peek(2) == TOK_DISABLE)
      rDisable();
    else
      next_token();
  }
  else if(token == TOK_CLOCKING)
  {
    rClocking();
  }
  else if(token == TOK_COVERGROUP)
  {
    rCoverGroup();
  }
  else if(may_be_type(token))
  {
    rDeclaration();
  }
  else if(
    token == TOK_VAR || token == TOK_WIRE || token == TOK_TRI0 ||
    token == TOK_TRI1 || token == TOK_INPUT || token == TOK_INOUT ||
    token == TOK_OUTPUT || token == TOK_GENVAR || token == TOK_TYPEDEF ||
    token == TOK_PARAMETER || token == TOK_LOCALPARAM ||
    token == TOK_DEFPARAM || token == TOK_SUPPLY0 || token == TOK_SUPPLY1 ||
    token == TOK_LET || token == TOK_ALIAS || token == TOK_RAND ||
    token == TOK_RANDC || token == TOK_LOCAL || token == TOK_PROTECTED ||
    token == TOK_AUTOMATIC || token == TOK_CONST)
  {
    rDeclaration();
  }
  else if(token == TOK_STATIC)
  {
    if(peek(2) == TOK_CONSTRAINT)
      rConstraint();
    else
      rDeclaration();
  }
  else if(token == TOK_EXPORT)
  {
    if(peek(2) == TOK_FUNCTION)
      rTaskFunction();
    else
    {
      skip_until(';');
    }
  }
  else if(
    token == TOK_FUNCTION || token == TOK_TASK || token == TOK_VIRTUAL ||
    token == TOK_EXTERN)
  {
    rTaskFunction();
  }
  else if(token == TOK_CONSTRAINT)
    rConstraint();
  else if(token == TOK_ASSIGN)
    rContinuousAssign();
  else if(token == TOK_FORK)
    rFork();
  else if(token == TOK_WAIT || token == TOK_WAIT_ORDER)
    rWait();
  else if(token == TOK_IF)
    rGenerateIf();
  else if(token == TOK_BEGIN)
    rGenerateBegin();
  else if(token == TOK_FOR)
    rGenerateFor();
  else if(token == TOK_GENERATE)
    rGenerate();
  else if(token == TOK_ASSERT || token == TOK_ASSUME || token == TOK_COVER)
    rAssertAssumeCover();
  else if(
    token == TOK_BUF || token == TOK_OR || token == TOK_NOR ||
    token == TOK_XOR || token == TOK_XNOR || token == TOK_AND ||
    token == TOK_NAND || token == TOK_NOT || token == TOK_BUFIF0 ||
    token == TOK_BUFIF1 || token == TOK_TRAN || token == TOK_TRANIF0 ||
    token == TOK_TRANIF1 || token == TOK_RTRAN || token == TOK_RTRANIF0 ||
    token == TOK_RTRANIF1 || token == TOK_PULLUP || token == TOK_PULLDOWN)
  {
    rModuleInstance();
  }
  else if(token.is_identifier())
  {
    // Type identifier (for declaration), label, module instance.
    // We look one further token ahead to disambiguate.
    auto &second_token = peek(2);
    auto &third_token = peek(3);
    if(second_token == '#' || second_token == '(')
    {
      // module #(...) instance(...);
      // module (...);
      rModuleInstance();
    }
    else if(second_token.is_identifier() && third_token == '(')
    {
      // module instance(...);
      rModuleInstance();
    }
    else if(second_token == TOK_COLON)
      rLabeledItem();
    else
    {
      // type identifier;
      rDeclaration();
    }
  }
  else if(token == TOK_TIMEUNIT)
  {
    skip_until(';');
  }
  else if(token == TOK_TIMEPRECISION)
  {
    skip_until(';');
  }
  else if(token == ';')
  {
    // the empty item
    next_token();
  }
  else if(token.is_system_identifier())
  {
    // $error...
    skip_until(';');
  }
  else if(token == TOK_IMPORT)
  {
    skip_until(';');
  }
  else if(token == '(')
  {
    // possibly a macro that wasn't found
    std::cout << "LPAREN: " << verilog_parser.get_file() << ':'
              << verilog_parser.get_line_no() << ' ' << token.text << "\n";
    rParenExpression();
  }
  else
  {
    // something else
    std::cout << "ELSE: " << verilog_parser.get_file() << ':'
              << verilog_parser.get_line_no() << ' ' << token.text << "\n";
    next_token();
  }
}

void verilog_indexer_parsert::rImport()
{
  next_token(); // import
  skip_until(';');
}

void verilog_indexer_parsert::rExtends()
{
  next_token(); // extends
  next_token(); // identifier
}

void verilog_indexer_parsert::rPorts()
{
  skip_until(';');
}

void verilog_indexer_parsert::rConstruct()
{
  auto keyword = next_token(); // initial, final, always, always_comb, ...
  rStatement();
}

void verilog_indexer_parsert::rClocking()
{
  if(peek() == TOK_DEFAULT)
    next_token(); // default

  if(next_token() != TOK_CLOCKING)
    return;

  skip_until(TOK_ENDCLOCKING);

  if(peek() == TOK_COLON)
  {
    // optional label
    next_token(); // :
    next_token(); // identifier
  }
}

void verilog_indexer_parsert::rCoverGroup()
{
  next_token(); // covergroup
  skip_until(TOK_ENDGROUP);

  if(peek() == TOK_COLON)
  {
    // optional label
    next_token(); // :
    next_token(); // identifier
  }
}

void verilog_indexer_parsert::rStatement()
{
  auto first = peek();
  if(first == TOK_ASSERT || first == TOK_ASSUME || first == TOK_COVER)
    rAssertAssumeCover();
  else if(first == TOK_BEGIN)
    rBegin();
  else if(first == TOK_CASE || first == TOK_CASEX || first == TOK_CASEZ)
    rCase();
  else if(first == TOK_UNIQUE || first == TOK_UNIQUE0 || first == TOK_PRIORITY)
    rUniquePriority();
  else if(first == TOK_FOR)
    rFor();
  else if(first == TOK_FOREACH)
    rForEach();
  else if(first == TOK_FOREVER)
    rForEver();
  else if(first == TOK_REPEAT)
    rRepeat();
  else if(first == TOK_WHILE)
    rWhile();
  else if(first == TOK_IF)
    rIf();
  else if(first == TOK_DISABLE)
    rDisable();
  else if(first == TOK_FORCE)
    rForce();
  else if(first == TOK_RELEASE)
    rRelease();
  else if(first == TOK_RETURN)
    rReturn();
  else if(first == '@')
  {
    next_token(); // @
    if(peek() == '(')
      rParenExpression();
    else if(peek() == TOK_PARENASTERIC) // (*
    {
      next_token();
      if(peek() == ')')
        next_token();
    }
    else
      next_token();

    rStatement();
  }
  else if(first == '#')
  {
    // delay
    next_token(); // #
    next_token(); // delay value
    rStatement();
  }
  else if(first == ';')
  {
    // skip
    next_token();
  }
  else
  {
    // Label?
    if(first.is_identifier() && peek(2) == TOK_COLON)
    {
      next_token(); // identifier
      next_token(); // :
      rStatement();
    }
    else
    {
      // e.g., declarations, assignments, ...
      skip_until(';');
    }
  }
}

void verilog_indexer_parsert::rAssertAssumeCover()
{
  next_token(); // assert, assume, ...

  if(peek() == TOK_FINAL)
    next_token();
  else if(peek() == TOK_PROPERTY)
    next_token();

  rParenExpression();

  if(peek() == TOK_ELSE)
  {
    next_token(); // else
    rStatement();
  }
  else
    skip_until(';');
}

void verilog_indexer_parsert::rBegin()
{
  next_token(); // begin

  if(peek() == TOK_COLON)
  {
    // optional block label
    next_token(); // :
    next_token(); // identifier
  }

  while(true)
  {
    if(peek().is_eof())
      return;

    if(peek() == TOK_END)
    {
      next_token(); // end
      break;
    }

    rStatement();
  }

  if(peek() == TOK_COLON)
  {
    // optional block label
    next_token(); // :
    next_token(); // identifier
  }
}

void verilog_indexer_parsert::rFork()
{
  next_token(); // fork

  if(peek() == TOK_COLON)
  {
    // optional block label
    next_token(); // :
    next_token(); // identifier
  }

  while(!peek().is_eof())
  {
    if(peek() == TOK_JOIN || peek() == TOK_JOIN_ANY || peek() == TOK_JOIN_NONE)
    {
      next_token();
      break;
    }

    rItem();
  }

  if(peek() == TOK_COLON)
  {
    // optional block label
    next_token(); // :
    next_token(); // identifier
  }
}

void verilog_indexer_parsert::rWait()
{
  next_token(); // wait, wait_order

  if(peek() == '(')
  {
    rParenExpression();
    rStatement();
  }
  else if(peek() == TOK_FORK)
  {
    next_token(); // fork
    if(next_token() != ';')
      return; // error
  }
  else
    return; // error
}

void verilog_indexer_parsert::rFor()
{
  next_token(); // for
  rParenExpression();
  rStatement();
}

void verilog_indexer_parsert::rForEach()
{
  next_token(); // foreach
  rParenExpression();
  rStatement();
}

void verilog_indexer_parsert::rForEver()
{
  next_token(); // forever
  rStatement();
}

void verilog_indexer_parsert::rRepeat()
{
  next_token(); // repeat
  rParenExpression();
  rStatement();
}

void verilog_indexer_parsert::rWhile()
{
  next_token(); // while
  rParenExpression();
  rStatement();
}

void verilog_indexer_parsert::rDisable()
{
  if(peek() == TOK_DEFAULT)
    next_token(); // default

  next_token(); // disable
  skip_until(';');
}

void verilog_indexer_parsert::rReturn()
{
  next_token(); // return
  skip_until(';');
}

void verilog_indexer_parsert::rBind()
{
  next_token(); // bind
  skip_until(';');
}

void verilog_indexer_parsert::rForce()
{
  next_token(); // force
  skip_until(';');
}

void verilog_indexer_parsert::rRelease()
{
  next_token(); // release
  skip_until(';');
}

void verilog_indexer_parsert::rModport()
{
  next_token(); // modport
  skip_until(';');
}

void verilog_indexer_parsert::rCell()
{
  next_token(); // cell
  skip_until(';');
}

void verilog_indexer_parsert::rDesign()
{
  next_token(); // design
  skip_until(';');
}

void verilog_indexer_parsert::rInterconnect()
{
  next_token(); // interconnect
  skip_until(';');
}

void verilog_indexer_parsert::rIf()
{
  next_token(); // if
  rParenExpression();
  rStatement();
  if(peek() == TOK_ELSE)
  {
    next_token();
    rStatement();
  }
}

void verilog_indexer_parsert::rCase()
{
  next_token(); // case, casex, ...
  rParenExpression();
  while(true)
  {
    if(peek().is_eof())
      return;
    if(peek() == TOK_ENDCASE)
    {
      next_token();
      return;
    }
    rCaseLabel();
    rStatement();
  }
}

void verilog_indexer_parsert::rCaseLabel()
{
  skip_until(TOK_COLON);
}

void verilog_indexer_parsert::rUniquePriority()
{
  // unique case/if ...
  // unique0 case/if ...
  // priority case/if ...
  auto first = next_token(); // unique, unique0, priority
  if(peek() == TOK_IF)
    rIf();
  else if(peek() == TOK_CASE || peek() == TOK_CASEZ || peek() == TOK_CASEX)
    rCase();
  else
  {
    // error
  }
}

void verilog_indexer_parsert::rParenExpression()
{
  auto first = next_token();
  if(first != '(')
    return;
  std::size_t count = 1;

  while(true)
  {
    auto token = next_token();
    if(token.is_eof())
      return;
    else if(token == '(')
      count++;
    else if(token == ')')
    {
      if(count == 1)
        return;
      count--;
    }
  }
}

void verilog_indexer_parsert::rDeclaration()
{
  if(peek() == TOK_PROTECTED)
  {
    next_token(); // protected
  }

  if(peek() == TOK_AUTOMATIC)
  {
    next_token(); // automatic
  }

  if(peek() == TOK_CONST)
  {
    next_token(); // const
  }

  auto &token = peek();

  if(token == TOK_TYPEDEF)
  {
    next_token(); // typedef
    rType();
  }
  else if(token == TOK_RAND || token == TOK_RANDC)
  {
    next_token(); // rand
    rType();
  }
  else if(token == TOK_LOCAL)
  {
    next_token(); // local
    rType();
  }
  else if(token == TOK_LET)
  {
    next_token(); // let
    rTypeOpt();
  }
  else if(token == TOK_ALIAS)
  {
    next_token(); // alias
    rTypeOpt();
  }
  else if(token == TOK_PARAMETER || token == TOK_LOCALPARAM)
  {
    next_token();
    rTypeOpt();
  }
  else if(
    token == TOK_VAR || token == TOK_INPUT || token == TOK_OUTPUT ||
    token == TOK_INOUT || token == TOK_WIRE || token == TOK_TRI0 ||
    token == TOK_TRI1)
  {
    next_token();
    rTypeOpt();
  }
  else
  {
    rType();
  }

  rDeclarators();
}

void verilog_indexer_parsert::rType()
{
  auto &token = peek();
  if(token == TOK_STRUCT || token == TOK_UNION)
  {
    rStructUnion();
  }
  else if(token == TOK_ENUM)
  {
    rEnum();
  }
  else
  {
    next_token();
  }
}

bool verilog_indexer_parsert::may_be_type(const tokent &token)
{
  return token == TOK_REG || token == TOK_GENVAR || token == TOK_ENUM ||
         token == TOK_INTEGER || token == TOK_REALTIME || token == TOK_REAL ||
         token == TOK_TIME || token == TOK_SIGNED || token == TOK_UNSIGNED ||
         token == TOK_SHORTREAL || token == TOK_BYTE || token == TOK_SHORTINT ||
         token == TOK_LONGINT || token == TOK_LOGIC || token == TOK_BIT ||
         token == TOK_INT || token == TOK_STRUCT || token == TOK_UNION ||
         token == TOK_STRING || token == TOK_VOID || token == TOK_EVENT ||
         token == TOK_CHANDLE;
}

void verilog_indexer_parsert::rTypeOpt()
{
  auto &token = peek();
  if(may_be_type(token))
    rType();
}

void verilog_indexer_parsert::rEnum()
{
  next_token();
  skip_until('{');
  skip_until('}');
}

void verilog_indexer_parsert::rStructUnion()
{
  next_token(); // struct or union
  skip_until('{');
  while(!peek().is_eof() && peek() != '}')
  {
    rType();
    rDeclarators();
  }
  skip_until('}');
}

void verilog_indexer_parsert::rDeclarators()
{
  skip_until(';');
}

void verilog_indexer_parsert::rTaskFunction()
{
  if(peek() == TOK_VIRTUAL)
    next_token(); // virtual

  if(peek() == TOK_EXTERN)
    next_token(); // extern

  if(peek() == TOK_EXPORT)
  {
    next_token(); // export
    next_token(); // string literal
  }

  auto tf_keyword = next_token(); // function or task

  if(peek() == TOK_AUTOMATIC)
    next_token(); // automatic

  // optional return type
  rTypeOpt();

  auto name = next_token(); // name or new

  {
    idt id;

    if(tf_keyword == TOK_FUNCTION)
      id.kind = idt::FUNCTION;
    else
      id.kind = idt::TASK;

    id.name = name.text;
    id.module = current_module;
    id.file_name = verilog_parser.get_file();
    id.line_number = verilog_parser.get_line_no();
    indexer.add(std::move(id));
  }

  if(tf_keyword == TOK_FUNCTION)
    skip_until(TOK_ENDFUNCTION);
  else
    skip_until(TOK_ENDTASK);

  // optional label
  if(peek() == TOK_COLON)
  {
    next_token(); // :
    next_token(); // identifier
  }
}

void verilog_indexer_parsert::rConstraint()
{
  if(peek() == TOK_STATIC)
  {
    next_token(); // static
  }

  next_token(); // constraint

  next_token(); // identifier

  if(next_token() != '{') // onstraint_block
    return;               // error

  skip_until('}');
}

void verilog_indexer_parsert::rContinuousAssign()
{
  skip_until(';');
}

void verilog_indexer_parsert::rGenerate()
{
  skip_until(TOK_ENDGENERATE);
}

void verilog_indexer_parsert::rGenerateFor()
{
  next_token(); // for
  rParenExpression();
  rItem();
}

void verilog_indexer_parsert::rGenerateIf()
{
  next_token(); // if
  rParenExpression();
  rItem();
  if(peek() == TOK_ELSE)
  {
    next_token();
    rItem();
  }
}

void verilog_indexer_parsert::rGenerateBegin()
{
  next_token(); // begin

  if(peek() == TOK_COLON)
  {
    // optional block label
    next_token(); // :
    next_token(); // identifier
  }

  while(true)
  {
    if(peek().is_eof())
      return;

    if(peek() == TOK_END)
    {
      next_token(); // end
      return;
    }

    rItem();
  }
}

void verilog_indexer_parsert::rProperty()
{
  next_token(); // property

  auto name = next_token(); // name

  {
    idt id;
    id.kind = idt::PROPERTY;
    id.name = name.text;
    id.module = current_module;
    id.file_name = verilog_parser.get_file();
    id.line_number = verilog_parser.get_line_no();
    indexer.add(std::move(id));
  }

  skip_until(TOK_ENDPROPERTY);

  // optional label
  if(peek() == TOK_COLON)
  {
    next_token(); // :
    next_token(); // identifier
  }
}

void verilog_indexer_parsert::rSequence()
{
  next_token(); // sequence

  auto name = next_token(); // name

  {
    idt id;
    id.kind = idt::SEQUENCE;
    id.name = name.text;
    id.module = current_module;
    id.file_name = verilog_parser.get_file();
    id.line_number = verilog_parser.get_line_no();
    indexer.add(std::move(id));
  }

  skip_until(TOK_ENDPROPERTY);

  // optional label
  if(peek() == TOK_COLON)
  {
    next_token(); // :
    next_token(); // identifier
  }
}

void verilog_indexer_parsert::rSpecify()
{
  skip_until(TOK_ENDSPECIFY);
}

void verilog_indexer_parsert::skip_until(int token)
{
  while(true)
  {
    if(peek().is_eof())
      return;
    if(next_token() == token)
      return;
  }
}

void verilog_indexer_parsert::rModuleInstance()
{
  auto first = next_token(); // module, class or primitive name

  if(peek() == '#')
  {
    // Module instance with parameters.
    next_token(); // #
    if(peek() == '(')
    {
      // parameter values
      rParenExpression();
    }
    else
    {
      next_token(); // parameter value
    }
  }

  // the instance name is optional
  if(peek() != '[' && peek() != '(')
  {
    auto second = next_token(); // instance name

    idt id;
    id.kind = verilog_indexert::idt::INSTANCE;
    id.name = second.text;
    id.module = current_module;
    id.file_name = verilog_parser.get_file();
    id.line_number = verilog_parser.get_line_no();
    id.instantiated_module = first.text;
    indexer.add(std::move(id));
  }

  if(peek() == '[') // instance range
    skip_until(']');

  if(peek() == '(') // connections
  {
    next_token(); // (
  }
  else if(peek() == '=') // initialization for classes
  {
    next_token(); // =
  }
  else
    return; // error

  skip_until(';');
}

void verilog_indexer_parsert::rLabeledItem()
{
  // label followed by assert/assume/cover
  next_token();                 // label
  if(next_token() != TOK_COLON) // :
    return;
  if(peek() == TOK_ASSERT || peek() == TOK_ASSUME || peek() == TOK_COVER)
    rAssertAssumeCover();
  else
    skip_until(';');
}
