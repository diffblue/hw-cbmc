/*******************************************************************\

Module: Verilog Synthesis

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <util/arith_tools.h>

#include "verilog_expr.h"
#include "verilog_typecheck.h"

/*******************************************************************\

Function: verilog_typecheckt::elaborate_generate_block

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::elaborate_generate_block(
  const verilog_generate_blockt &generate_block,
  module_itemst &dest)
{
  // These introduce a scope, and generate-for may append a
  // loop index to the label. We hence leave a generate_block
  // module item.
  bool is_named = generate_block.is_named();

  if(is_named)
    enter_named_block(generate_block.base_name());

  module_itemst new_module_items;

  for(auto &item : generate_block.module_items())
    elaborate_generate_item(item, new_module_items);

  auto identifier = generate_block.base_name();
  auto block = verilog_generate_blockt(identifier, std::move(new_module_items));
  block.add_source_location() = generate_block.source_location();

  dest.push_back(std::move(block));

  if(is_named)
    named_blocks.pop_back();
}

/*******************************************************************\

Function: verilog_typecheckt::elaborate_genvar_decl

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::elaborate_genvar_decl(
  const verilog_genvar_declt &genvar_decl,
  module_itemst &)
{
  symbolt symbol{irep_idt{}, verilog_genvar_typet{}, mode};

  symbol.module = module_identifier;
  symbol.value.make_nil();

  for(auto &declarator : genvar_decl.declarators())
  {
    DATA_INVARIANT(declarator.id() == ID_declarator, "must have declarator");

    symbol.base_name = declarator.base_name();
    symbol.location = declarator.source_location();

    if(symbol.base_name.empty())
      throw errort().with_location(genvar_decl.source_location())
        << "empty symbol name";

    symbol.name = hierarchical_identifier(symbol.base_name);
    symbol.pretty_name = strip_verilog_root_prefix(symbol.name);

    genvars[symbol.base_name] = -1;

    add_symbol(symbol);

    // When used in a for loop, these come with an initial value.
    if(declarator.has_value())
    {
      mp_integer rhs = convert_integer_constant_expression(declarator.value());

      if(rhs < 0)
      {
        throw errort().with_location(declarator.value().source_location())
          << "must not assign negative value to genvar";
      }

      genvars[symbol.base_name] = rhs;
    }
  }
}

/*******************************************************************\

Function: verilog_typecheckt::elaborate_generate_item

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

verilog_typecheckt::module_itemst verilog_typecheckt::elaborate_generate_item(
  const verilog_module_itemt &module_item)
{
  module_itemst dest;

  if(module_item.id() == ID_generate_assign)
    elaborate_generate_assign(to_verilog_generate_assign(module_item), dest);
  else if(module_item.id() == ID_generate_block)
    elaborate_generate_block(to_verilog_generate_block(module_item), dest);
  else if(module_item.id() == ID_verilog_case_generate)
    elaborate_case_generate(to_verilog_case_generate(module_item), dest);
  else if(module_item.id() == ID_verilog_genvar_decl)
    elaborate_genvar_decl(to_verilog_genvar_decl(module_item), dest);
  else if(module_item.id() == ID_generate_if)
    elaborate_generate_if(to_verilog_generate_if(module_item), dest);
  else if(module_item.id() == ID_generate_for)
    elaborate_generate_for(to_verilog_generate_for(module_item), dest);
  else
  {
    // E.g., declarations. Remember the values of the
    // generate variables.
    verilog_set_genvarst set_genvars(module_item);
    irept &variables = set_genvars.add("variables");

    for(const auto &it : genvars)
      variables.set(it.first, integer2string(it.second));

    dest = elaborate_level({set_genvars});
  }

  return dest;
}

void verilog_typecheckt::elaborate_generate_item(
  const verilog_module_itemt &module_item,
  module_itemst &dest)
{
  auto result = elaborate_generate_item(module_item);
  dest.insert(dest.end(), result.begin(), result.end());
}

/*******************************************************************\

Function: verilog_typecheckt::elaborate_case_generate

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::elaborate_case_generate(
  const verilog_case_generatet &case_generate,
  module_itemst &dest)
{
  auto construct_number =
    case_generate.get_size_t(ID_C_verilog_construct_number);

  // Evaluate the case expression
  mp_integer case_value =
    convert_integer_constant_expression(case_generate.case_expr());

  // Find the matching case item
  for(auto &case_item : case_generate.items())
  {
    if(!case_item.is_default())
    {
      for(auto &value : case_item.values())
      {
        mp_integer item_value = convert_integer_constant_expression(value);

        if(item_value == case_value)
        {
          // match
          elaborate_conditional_generate_branch(
            case_item.block(), construct_number, dest);
          return; // done
        }
      }
    }
  }

  // None found. Look for the first 'default'.
  for(auto &case_item : case_generate.items())
  {
    if(case_item.is_default())
    {
      // match
      elaborate_conditional_generate_branch(
        case_item.block(), construct_number, dest);
      return; // done
    }
  }
}

/*******************************************************************\

Function: verilog_typecheckt::elaborate_generate_if

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::elaborate_generate_if(
  const verilog_generate_ift &statement,
  module_itemst &dest)
{
  if(statement.operands().size()!=3 &&
     statement.operands().size()!=2)
  {
    throw errort().with_location(statement.source_location())
      << "generate_if expects two or three operands";
  }

  auto construct_number = statement.get_size_t(ID_C_verilog_construct_number);

  mp_integer condition =
    convert_integer_constant_expression(to_multi_ary_expr(statement).op0());

  if(condition==0)
  {
    if(statement.operands().size()==3)
      elaborate_conditional_generate_branch(
        to_verilog_module_item(to_multi_ary_expr(statement).op2()),
        construct_number,
        dest);
  }
  else
    elaborate_conditional_generate_branch(
      to_verilog_module_item(to_multi_ary_expr(statement).op1()),
      construct_number,
      dest);
}

/*******************************************************************\

Function: verilog_typecheckt::elaborate_generate_assign

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::elaborate_generate_assign(
  const verilog_generate_assignt &statement,
  module_itemst &dest)
{
  if(statement.lhs().id() != ID_verilog_identifier)
  {
    throw errort().with_location(statement.lhs().source_location())
      << "expected symbol on left hand side of assignment";
  }

  const irep_idt &identifier =
    to_verilog_identifier_expr(statement.lhs()).base_name();

  genvarst::iterator it=genvars.find(identifier);
  
  if(it==genvars.end())
  {
    throw errort().with_location(statement.lhs().source_location())
      << "expected genvar on left hand side of assignment";
  }

  mp_integer rhs = convert_integer_constant_expression(statement.rhs());

  if(rhs<0)
  {
    throw errort().with_location(statement.rhs().source_location())
      << "must not assign negative value to genvar";
  }
  
  it->second=rhs;
}

/*******************************************************************\

Function: verilog_typecheckt::generate_for_loop_index

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt verilog_typecheckt::generate_for_loop_index(
  const verilog_module_itemt &initialization) const
{
  if(initialization.id() == ID_generate_assign)
  {
    auto &assignment = to_verilog_generate_assign(initialization);
    return assignment.lhs();
  }
  else if(initialization.id() == ID_verilog_genvar_decl)
  {
    auto &decl = to_verilog_genvar_decl(initialization);
    PRECONDITION(decl.declarators().size() == 1);
    return decl.declarators().front().verilog_identifier_expr();
  }
  else
  {
    throw errort().with_location(initialization.source_location())
      << "failed to determine generate loop index";
  }
}

static void number_generate_block(verilog_module_itemt &);

/*******************************************************************\

Function: number_conditional_generate_construct

  Inputs: a conditional generate construct, and its number

 Outputs:

 Purpose: A conditional generate construct that is the single item of
          a branch without begin-end is directly nested, 1800-2017
          27.5, and is part of the enclosing construct, whose number it
          shares. Any other branch is a generate block, and hence a
          scope.

\*******************************************************************/

static void number_conditional_generate_construct(
  verilog_module_itemt &construct,
  std::size_t number)
{
  construct.set_size_t(ID_C_verilog_construct_number, number);

  auto number_branch = [number](verilog_module_itemt &branch)
  {
    if(branch.id() == ID_generate_if || branch.id() == ID_verilog_case_generate)
      number_conditional_generate_construct(branch, number);
    else
      number_generate_block(branch);
  };

  if(construct.id() == ID_generate_if)
  {
    for(std::size_t i = 1; i < construct.get_sub().size(); i++)
      number_branch(
        static_cast<verilog_module_itemt &>(construct.get_sub()[i]));
  }
  else
  {
    for(auto &case_item : to_verilog_case_generate(construct).items())
      number_branch(case_item.block());
  }
}

/*******************************************************************\

Function: number_generate_constructs

  Inputs: an item of a scope, and the number of the last generate
          construct of the scope before the item

 Outputs:

 Purpose: Number the generate constructs of the given item, see
          verilog_typecheckt::number_generate_constructs.

\*******************************************************************/

static void
number_generate_constructs(verilog_module_itemt &item, std::size_t &counter)
{
  if(item.id() == ID_generate_for)
  {
    item.set_size_t(ID_C_verilog_construct_number, ++counter);
    number_generate_block(
      static_cast<verilog_module_itemt &>(item.get_sub()[3]));
  }
  else if(item.id() == ID_generate_if || item.id() == ID_verilog_case_generate)
  {
    number_conditional_generate_construct(item, ++counter);
  }
  else if(item.id() == ID_generate_block)
  {
    auto &generate_block = to_verilog_generate_block(item);

    // A generate region, which is not a scope, 1800-2017 27.6, unlike a
    // named generate block.
    if(generate_block.is_named())
      number_generate_block(item);
    else
    {
      for(auto &sub_item : generate_block.module_items())
        number_generate_constructs(sub_item, counter);
    }
  }
}

/*******************************************************************\

Function: number_generate_block

  Inputs: the generate block of a generate construct

 Outputs:

 Purpose: The generate block of a generate construct is a scope, which
          has its own numbering of the generate constructs in it. This
          applies to a single item without begin-end as well.

\*******************************************************************/

static void number_generate_block(verilog_module_itemt &block)
{
  std::size_t counter = 0;

  if(block.id() == ID_generate_block)
  {
    for(auto &item : to_verilog_generate_block(block).module_items())
      number_generate_constructs(item, counter);
  }
  else
    number_generate_constructs(block, counter);
}

/*******************************************************************\

Function: verilog_typecheckt::number_generate_constructs

  Inputs: the module items of a design element

 Outputs:

 Purpose: 1800-2017 27.6: the generate constructs of a scope are
          numbered in the order in which they appear, starting with 1,
          named or not. An unnamed generate block of a construct is
          named after the number of the construct, see
          unnamed_generate_block_name. A conditional generate construct
          that is directly nested in another one, 27.5, shares the
          number of the latter. The numbers are recorded on the
          constructs before the elaboration.

\*******************************************************************/

void verilog_typecheckt::number_generate_constructs(module_itemst &module_items)
{
  std::size_t counter = 0;

  for(auto &item : module_items)
    ::number_generate_constructs(item, counter);
}

/*******************************************************************\

Function: as_generate_block

  Inputs:

 Outputs:

 Purpose: The generate block that the given body of a generate
          construct is: the body itself if it has begin-end, or else
          an unnamed generate block with the single item, 1800-2017
          27.5 and 27.6.

\*******************************************************************/

static verilog_generate_blockt
as_generate_block(const verilog_module_itemt &body)
{
  if(body.id() == ID_generate_block)
    return to_verilog_generate_block(body);

  verilog_generate_blockt generate_block{{body}};
  generate_block.add_source_location() = body.source_location();
  return generate_block;
}

/*******************************************************************\

Function: verilog_typecheckt::elaborate_conditional_generate_branch

  Inputs:

 Outputs:

 Purpose: Elaborate the chosen branch of a conditional generate
          construct. A branch that is a conditional generate construct
          without begin-end is directly nested, 1800-2017 27.5. Any
          other branch is a generate block, which is a scope, also when
          it is a single item without begin-end, and is named genblk<n>
          if it has no name, 1800-2017 27.6.

\*******************************************************************/

void verilog_typecheckt::elaborate_conditional_generate_branch(
  const verilog_module_itemt &branch,
  std::size_t construct_number,
  module_itemst &dest)
{
  if(branch.id() == ID_generate_if || branch.id() == ID_verilog_case_generate)
  {
    elaborate_generate_item(branch, dest);
    return;
  }

  auto generate_block = as_generate_block(branch);
  if(!generate_block.is_named())
    generate_block.base_name(unnamed_generate_block_name(construct_number));

  elaborate_generate_item(generate_block, dest);
}

/*******************************************************************\

Function: verilog_typecheckt::unnamed_generate_block_name

  Inputs:

 Outputs:

 Purpose: The name of an unnamed generate block of the generate
          construct with the given number, 1800-2017 27.6: genblk<n>,
          with leading zeros added to the number until the name does
          not conflict with a name declared in the scope.

\*******************************************************************/

irep_idt
verilog_typecheckt::unnamed_generate_block_name(std::size_t construct_number)
{
  DATA_INVARIANT(
    construct_number != 0, "generate constructs are numbered from 1");

  std::string number = std::to_string(construct_number);

  while(true)
  {
    irep_idt name = "genblk" + number;
    if(
      symbol_table.symbols.find(hierarchical_identifier(name)) ==
      symbol_table.symbols.end())
    {
      return name;
    }
    number = '0' + number;
  }
}

/*******************************************************************\

Function: verilog_typecheckt::add_loop_index_symbol

  Inputs:

 Outputs:

 Purpose: Add the implicit localparam with the name of the loop index
          to a generate block of a loop generate construct,
          1800-2017 27.4. It is a genvar symbol, and hence takes the
          value of the genvar that is recorded for the items of the
          block.

\*******************************************************************/

void verilog_typecheckt::add_loop_index_symbol(
  const irep_idt &block_base_name,
  const exprt &loop_index)
{
  auto &base_name = to_verilog_identifier_expr(loop_index).base_name();

  symbolt symbol{
    hierarchical_identifier(
      id2string(block_base_name) + '.' + id2string(base_name)),
    verilog_genvar_typet{},
    mode};

  symbol.base_name = base_name;
  symbol.module = module_identifier;
  symbol.value.make_nil();
  symbol.location = loop_index.source_location();
  symbol.pretty_name = strip_verilog_root_prefix(symbol.name);

  add_symbol(std::move(symbol));
}

/*******************************************************************\

Function: verilog_typecheckt::elaborate_generate_for

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void verilog_typecheckt::elaborate_generate_for(
  const verilog_generate_fort &for_statement,
  module_itemst &dest)
{
  auto construct_number =
    for_statement.get_size_t(ID_C_verilog_construct_number);

  // 1800-2017 27.6: a generate loop with a block name yields an array of
  // generate blocks, the individual blocks being named block_name[0],
  // block_name[1], and so on.  The array itself is a scope that
  // hierarchical identifiers can select from, hence gets a symbol.
  // A block without a name is given the name genblk<n>, where n is the
  // number of the loop among the generate constructs of the scope. This
  // includes a body that is a single item without begin-end, 27.4.
  const auto body = as_generate_block(for_statement.body());

  const irep_idt block_name = body.is_named()
                                ? body.base_name()
                                : unnamed_generate_block_name(construct_number);

  add_named_block_symbol(block_name, body.source_location());

  // 1800-2017 27.4: a genvar that is declared in the header of the loop is
  // local to the loop, and hence two loops in the same scope may declare a
  // genvar with the same name. We declare it in the scope of the array of
  // generate blocks, which is entered when the header of the loop is
  // evaluated.
  const bool genvar_in_loop_scope =
    for_statement.init().id() == ID_verilog_genvar_decl;

  auto enter_loop_scope = [this, genvar_in_loop_scope, &block_name]()
  {
    if(genvar_in_loop_scope)
      enter_named_block(block_name);
  };

  auto leave_loop_scope = [this, genvar_in_loop_scope]()
  {
    if(genvar_in_loop_scope)
      named_blocks.pop_back();
  };

  // The genvar must still not clash with a name in the scope that contains
  // the loop.
  if(genvar_in_loop_scope)
  {
    auto &genvar_decl = to_verilog_genvar_decl(for_statement.init());
    for(auto &declarator : genvar_decl.declarators())
    {
      auto existing =
        symbol_table.lookup(hierarchical_identifier(declarator.base_name()));
      if(existing != nullptr)
      {
        throw errort().with_location(declarator.source_location())
          << "definition of symbol `" << declarator.base_name()
          << "' conflicts with earlier definition at line "
          << existing->location.get_line();
      }
    }
  }

  enter_loop_scope();
  elaborate_generate_item(for_statement.init(), dest);

  // work out what the loop index is
  auto loop_index = generate_for_loop_index(for_statement.init());
  leave_loop_scope();

  while(true)
  {
    enter_loop_scope();
    mp_integer condition =
      convert_integer_constant_expression(for_statement.cond());
    const mp_integer loop_index_int =
      condition == 0 ? 0 : convert_integer_constant_expression(loop_index);
    leave_loop_scope();

    if(condition==0) break;

    // Order is important!
    // First execute the block, whose identifier is that of the loop
    // with the loop counter appended, surrounded by square brackets.
    auto copy_of_body = body;
    auto new_base_name =
      id2string(block_name) + '[' + integer2string(loop_index_int) + ']';
    copy_of_body.base_name(new_base_name);

    // 1800-2017 27.4: each generate block of the loop has an implicit
    // localparam with the name of the loop index, whose value is that
    // of the loop index for that block. The value of the genvar is
    // recorded when the block is elaborated.
    if(genvar_in_loop_scope)
      add_loop_index_symbol(new_base_name, loop_index);

    elaborate_generate_item(copy_of_body, dest);

    // Now increase/decrease the loop counter.
    enter_loop_scope();
    {
      auto statement = for_statement.iteration().id();
      if(statement == ID_generate_assign)
      {
        elaborate_generate_assign(
          to_verilog_generate_assign(for_statement.iteration()), dest);
      }
      else if(statement == ID_preincrement || statement == ID_predecrement)
      {
        // turn ++x and x++ into x = x + 1
        // turn --x and x-- into x = x - 1
        // The expressions are parse trees, prior to typechecking
        auto &op = to_unary_expr(for_statement.iteration()).op();
        auto one = constant_exprt{ID_1, typet{}};
        auto new_value = binary_exprt{
          op, statement == ID_preincrement ? ID_plus : ID_minus, one, typet{}};
        auto assignment = verilog_generate_assignt{op, new_value};

        elaborate_generate_assign(assignment, dest);
      }
      else
      {
        DATA_INVARIANT_WITH_DIAGNOSTICS(
          false,
          "unexpected genvar_iteration item",
          for_statement.iteration().pretty());
      }
    }
    leave_loop_scope();
  }
}
