/*******************************************************************\

Module: AIGER Language Interface

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// AIGER Language Interface

#include "aiger_ebmc_language.h"

extern "C"
{
#include <ic3/aiger/aiger.h>
}

#include <util/bitvector_types.h>
#include <util/cmdline.h>
#include <util/mathematical_expr.h>
#include <util/message.h>
#include <util/std_expr.h>

#include <ebmc/ebmc_error.h>
#include <ebmc/transition_system.h>
#include <temporal-logic/ltl.h>
#include <trans-word-level/next_symbol.h>

#include <iostream>

static std::string lit_name(const char *name, const char *prefix, unsigned i)
{
  if(name != nullptr)
    return name;
  return std::string(prefix) + std::to_string(i);
}

/// Convert an AIGER literal to an exprt.
static exprt
lit_to_expr(unsigned lit, const std::map<unsigned, irep_idt> &var_map)
{
  if(lit == 0)
    return false_exprt{};
  if(lit == 1)
    return true_exprt{};

  unsigned var = lit >> 1;
  bool negated = (lit & 1) != 0;

  auto it = var_map.find(var);
  INVARIANT(it != var_map.end(), "AIGER literal must map to a known variable");

  symbol_exprt sym{it->second, bool_typet{}};

  if(negated)
    return not_exprt{sym};
  else
    return std::move(sym);
}

static void show_aiger_parse(const struct aiger &model, std::ostream &out)
{
  out << "AIGER model" << '\n'
      << "  Variables: " << model.maxvar << '\n'
      << "  Inputs:    " << model.num_inputs << '\n'
      << "  Latches:   " << model.num_latches << '\n'
      << "  Outputs:   " << model.num_outputs << '\n'
      << "  AND gates: " << model.num_ands << '\n'
      << "  Bad:       " << model.num_bad << '\n'
      << "  Constraints: " << model.num_constraints << '\n'
      << "  Justice:   " << model.num_justice << '\n'
      << "  Fairness:  " << model.num_fairness << '\n';

  for(std::size_t i = 0; i < model.num_inputs; i++)
  {
    out << "  Input " << i << ": lit=" << model.inputs[i].lit;
    if(model.inputs[i].name != nullptr)
      out << " name=" << model.inputs[i].name;
    out << '\n';
  }

  for(std::size_t i = 0; i < model.num_latches; i++)
  {
    out << "  Latch " << i << ": lit=" << model.latches[i].lit
        << " next=" << model.latches[i].next
        << " reset=" << model.latches[i].reset;
    if(model.latches[i].name != nullptr)
      out << " name=" << model.latches[i].name;
    out << '\n';
  }

  for(std::size_t i = 0; i < model.num_outputs; i++)
  {
    out << "  Output " << i << ": lit=" << model.outputs[i].lit;
    if(model.outputs[i].name != nullptr)
      out << " name=" << model.outputs[i].name;
    out << '\n';
  }

  for(std::size_t i = 0; i < model.num_ands; i++)
  {
    out << "  AND " << i << ": " << model.ands[i].lhs << " = "
        << model.ands[i].rhs0 << " & " << model.ands[i].rhs1 << '\n';
  }
}

/// Build the symbol table from the parsed AIGER data and
/// return the transition system.
static transition_systemt build_transition_system(const struct aiger &model)
{
  const irep_idt mode = "AIGER";
  const irep_idt module_id = "aiger::main";

  transition_systemt result;

  // Map from AIGER variable index to symbol identifier
  std::map<unsigned, irep_idt> var_map;

  // Inputs
  for(std::size_t i = 0; i < model.num_inputs; i++)
  {
    std::string name = lit_name(model.inputs[i].name, "input", i);
    irep_idt id = id2string(module_id) + "::" + name;

    symbolt symbol{id, bool_typet(), mode};
    symbol.base_name = name;
    symbol.pretty_name = name;
    symbol.module = module_id;
    symbol.is_input = true;
    symbol.is_state_var = false;

    auto add_result = result.symbol_table.add(symbol);
    CHECK_RETURN(!add_result);

    var_map[model.inputs[i].lit >> 1] = id;
  }

  // Latches
  for(std::size_t i = 0; i < model.num_latches; i++)
  {
    std::string name = lit_name(model.latches[i].name, "latch", i);
    irep_idt id = id2string(module_id) + "::" + name;

    symbolt symbol{id, bool_typet(), mode};
    symbol.base_name = name;
    symbol.pretty_name = name;
    symbol.module = module_id;
    symbol.is_input = false;
    symbol.is_state_var = true;

    auto add_result = result.symbol_table.add(symbol);
    CHECK_RETURN(!add_result);

    var_map[model.latches[i].lit >> 1] = id;
  }

  // AND gates
  for(std::size_t i = 0; i < model.num_ands; i++)
  {
    unsigned lhs_var = model.ands[i].lhs >> 1;
    irep_idt id = id2string(module_id) + "::and" + std::to_string(i);

    symbolt symbol{id, bool_typet(), mode};
    symbol.base_name = "and" + std::to_string(i);
    symbol.pretty_name = symbol.base_name;
    symbol.module = module_id;
    symbol.is_input = false;
    symbol.is_state_var = false;

    auto add_result = result.symbol_table.add(symbol);
    CHECK_RETURN(!add_result);

    var_map[lhs_var] = id;
  }

  // Build transition relation components
  exprt::operandst invar_exprs;
  exprt::operandst init_exprs;
  exprt::operandst trans_exprs;

  invar_exprs.reserve(model.num_ands + model.num_outputs);
  init_exprs.reserve(model.num_latches);
  trans_exprs.reserve(model.num_latches);

  // AND gate definitions as invariants
  for(std::size_t i = 0; i < model.num_ands; i++)
  {
    exprt lhs = lit_to_expr(model.ands[i].lhs, var_map);
    exprt rhs0 = lit_to_expr(model.ands[i].rhs0, var_map);
    exprt rhs1 = lit_to_expr(model.ands[i].rhs1, var_map);
    invar_exprs.push_back(equal_exprt{lhs, and_exprt{rhs0, rhs1}});
  }

  // Latch initial states and transitions
  for(std::size_t i = 0; i < model.num_latches; i++)
  {
    irep_idt latch_id = var_map[model.latches[i].lit >> 1];
    symbol_exprt latch_sym(latch_id, bool_typet());

    unsigned reset = model.latches[i].reset;
    if(reset == 0)
      init_exprs.push_back(equal_exprt{latch_sym, false_exprt{}});
    else if(reset == 1)
      init_exprs.push_back(equal_exprt{latch_sym, true_exprt{}});
    else
      throw ebmc_errort{} << "unexpected AIGER reset value";

    exprt next_val = lit_to_expr(model.latches[i].next, var_map);
    next_symbol_exprt next_latch{latch_sym};
    trans_exprs.push_back(equal_exprt{next_latch, next_val});
  }

  // Outputs and properties.
  // In AIGER 1.0, outputs are bad-state signals (output=1 means bad).
  // In AIGER 1.9+, explicit 'bad' signals are used instead.
  bool outputs_are_properties = (model.num_bad == 0 && model.num_outputs > 0);

  for(std::size_t i = 0; i < model.num_outputs; i++)
  {
    std::string name = lit_name(model.outputs[i].name, "output", i);
    irep_idt id = id2string(module_id) + "::" + name;

    symbolt symbol{id, bool_typet(), mode};
    symbol.base_name = name;
    symbol.pretty_name = name;
    symbol.module = module_id;
    symbol.is_input = false;
    symbol.is_state_var = false;

    {
      auto add_result = result.symbol_table.add(symbol);
      CHECK_RETURN(!add_result);
    }

    exprt out_val = lit_to_expr(model.outputs[i].lit, var_map);
    invar_exprs.push_back(equal_exprt{symbol_exprt{id, bool_typet{}}, out_val});

    if(outputs_are_properties)
    {
      // G(!output), i.e., the output should never be true
      irep_idt prop_id =
        id2string(module_id) + "::spec::output" + std::to_string(i);

      symbolt prop_symbol{prop_id, bool_typet(), mode};
      prop_symbol.base_name = name;
      prop_symbol.pretty_name = name;
      prop_symbol.module = module_id;
      prop_symbol.is_property = true;
      prop_symbol.value = G_exprt{not_exprt{symbol_exprt{id, bool_typet{}}}};

      auto add_result = result.symbol_table.add(prop_symbol);
      CHECK_RETURN(!add_result);
    }
  }

  // Bad state properties (AIGER 1.9+)
  for(std::size_t i = 0; i < model.num_bad; i++)
  {
    std::string name = lit_name(model.bad[i].name, "bad", i);
    irep_idt prop_id = id2string(module_id) + "::spec::bad" + std::to_string(i);

    exprt bad_expr = lit_to_expr(model.bad[i].lit, var_map);

    symbolt prop_symbol{prop_id, bool_typet(), mode};
    prop_symbol.base_name = name;
    prop_symbol.pretty_name = name;
    prop_symbol.module = module_id;
    prop_symbol.is_property = true;
    prop_symbol.value = G_exprt{not_exprt{bad_expr}};

    auto add_result = result.symbol_table.add(prop_symbol);
    CHECK_RETURN(!add_result);
  }

  // Justice properties (liveness): GF(l1 ∧ l2 ∧ ...)
  for(std::size_t i = 0; i < model.num_justice; i++)
  {
    std::string name = lit_name(model.justice[i].name, "justice", i);
    irep_idt prop_id =
      id2string(module_id) + "::spec::justice" + std::to_string(i);

    exprt::operandst conjuncts;
    for(std::size_t j = 0; j < model.justice[i].size; j++)
      conjuncts.push_back(lit_to_expr(model.justice[i].lits[j], var_map));

    symbolt prop_symbol{prop_id, bool_typet(), mode};
    prop_symbol.base_name = name;
    prop_symbol.pretty_name = name;
    prop_symbol.module = module_id;
    prop_symbol.is_property = true;
    prop_symbol.value = G_exprt{F_exprt{conjunction(conjuncts)}};

    auto add_result = result.symbol_table.add(prop_symbol);
    CHECK_RETURN(!add_result);
  }

  // Fairness properties (liveness): GF(lit)
  for(std::size_t i = 0; i < model.num_fairness; i++)
  {
    std::string name = lit_name(model.fairness[i].name, "fairness", i);
    irep_idt prop_id =
      id2string(module_id) + "::spec::fairness" + std::to_string(i);

    exprt fair_expr = lit_to_expr(model.fairness[i].lit, var_map);

    symbolt prop_symbol{prop_id, bool_typet(), mode};
    prop_symbol.base_name = name;
    prop_symbol.pretty_name = name;
    prop_symbol.module = module_id;
    prop_symbol.is_property = true;
    prop_symbol.value = G_exprt{F_exprt{fair_expr}};

    auto add_result = result.symbol_table.add(prop_symbol);
    CHECK_RETURN(!add_result);
  }

  // Module symbol
  typet module_type(ID_module);

  symbolt module_symbol{module_id, module_type, mode};
  module_symbol.base_name = "main";
  module_symbol.pretty_name = "main";
  module_symbol.module = module_id;
  module_symbol.value = transt{
    ID_trans,
    conjunction(invar_exprs),
    conjunction(init_exprs),
    conjunction(trans_exprs),
    module_type};

  {
    auto add_result = result.symbol_table.add(module_symbol);
    CHECK_RETURN(!add_result);
  }

  result.main_symbol = &result.symbol_table.lookup_ref(module_id);
  result.trans_expr = to_trans_expr(result.main_symbol->value);

  return result;
}

std::optional<transition_systemt> aiger_ebmc_languaget::transition_system()
{
  if(cmdline.args.empty())
    throw ebmc_errort{} << "no file name given";

  if(cmdline.args.size() >= 2)
    throw ebmc_errort{}.with_exit_code(1) << "AIGER only uses a single file";

  const auto &file_name = cmdline.args.front();

  // Parse
  struct aiger *model = aiger_init();

  const char *error = aiger_open_and_read_from_file(model, file_name.c_str());

  if(error != nullptr)
  {
    std::string error_msg = error;
    aiger_reset(model);
    throw ebmc_errort{}.with_exit_code(1)
      << "AIGER parsing error: " << error_msg;
  }

  if(cmdline.isset("show-parse"))
  {
    show_aiger_parse(*model, std::cout);
    aiger_reset(model);
    return {};
  }

  auto result = build_transition_system(*model);
  aiger_reset(model);

  if(cmdline.isset("show-symbol-table"))
  {
    std::cout << result.symbol_table;
    return {};
  }

  return result;
}
