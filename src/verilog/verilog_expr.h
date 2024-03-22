/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_VERILOG_EXPR_H
#define CPROVER_VERILOG_EXPR_H

#include <util/std_expr.h>

/// The syntax for these A.B, where A is a module identifier and B
/// is an identifier within that module. B is given als symbol_exprt.
class hierarchical_identifier_exprt : public binary_exprt
{
public:
  const exprt &module() const
  {
    return op0();
  }

  const symbol_exprt &item() const
  {
    return static_cast<const symbol_exprt &>(binary_exprt::op1());
  }

  const symbol_exprt &rhs() const
  {
    return item();
  }

  const irep_idt &identifier() const
  {
    return get(ID_identifier);
  }

  void identifier(irep_idt _identifier)
  {
    set(ID_identifier, _identifier);
  }

protected:
  using binary_exprt::op0;
  using binary_exprt::op1;
};

inline const hierarchical_identifier_exprt &
to_hierarchical_identifier_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_hierarchical_identifier);
  binary_exprt::check(expr);
  return static_cast<const hierarchical_identifier_exprt &>(expr);
}

inline hierarchical_identifier_exprt &
to_hierarchical_identifier_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_hierarchical_identifier);
  binary_exprt::check(expr);
  return static_cast<hierarchical_identifier_exprt &>(expr);
}

class function_call_exprt : public binary_exprt
{
public:
  exprt &function() { return op0(); }
  const exprt &function() const { return op0(); }
  
  typedef exprt::operandst argumentst;

  argumentst &arguments()
  {
    return op1().operands();
  }

  const argumentst &arguments() const
  {
    return op1().operands();
  }

  bool is_system_function_call() const;
};

inline const function_call_exprt &to_function_call_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_function_call);
  binary_exprt::check(expr);
  return static_cast<const function_call_exprt &>(expr);
}

inline function_call_exprt &to_function_call_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_function_call);
  binary_exprt::check(expr);
  return static_cast<function_call_exprt &>(expr);
}

class verilog_statementt:public exprt
{
public:
  explicit verilog_statementt(const irep_idt &id):exprt(id)
  {
  }

  verilog_statementt(const irep_idt &id, operandst _operands) : exprt(id)
  {
    operands() = std::move(_operands);
  }

  verilog_statementt(
    const irep_idt &id,
    operandst _operands,
    source_locationt __source_location)
    : exprt(id)
  {
    operands() = std::move(_operands);
    if(__source_location.is_not_nil())
      add_source_location() = std::move(__source_location);
  }

  verilog_statementt()
  {
  }
};

inline const verilog_statementt &to_verilog_statement(const exprt &expr)
{
  return static_cast<const verilog_statementt &>(expr);
}

inline verilog_statementt &to_verilog_statement(exprt &expr)
{
  return static_cast<verilog_statementt &>(expr);
}

class verilog_module_exprt : public exprt
{
public:
  using module_itemst = std::vector<class verilog_module_itemt>;

  verilog_module_exprt() : exprt(ID_verilog_module)
  {
  }

  explicit verilog_module_exprt(module_itemst _module_items)
    : verilog_module_exprt()
  {
    module_items() = std::move(_module_items);
  }

  const module_itemst &module_items() const
  {
    return (const module_itemst &)(operands());
  }

  module_itemst &module_items()
  {
    return (module_itemst &)(operands());
  }
};

inline const verilog_module_exprt &to_verilog_module_expr(const exprt &expr)
{
  return static_cast<const verilog_module_exprt &>(expr);
}

inline verilog_module_exprt &to_verilog_module_expr(exprt &expr)
{
  return static_cast<verilog_module_exprt &>(expr);
}

class verilog_module_itemt:public exprt
{
public:
  inline explicit verilog_module_itemt(const irep_idt &id):exprt(id)
  {
  }
  
  inline verilog_module_itemt()
  {
  }
};

inline const verilog_module_itemt &to_verilog_module_item(const irept &irep)
{
  return static_cast<const verilog_module_itemt &>(irep);
}

inline verilog_module_itemt &to_verilog_module_item(irept &irep)
{
  return static_cast<verilog_module_itemt &>(irep);
}

class verilog_generate_assignt : public verilog_module_itemt
{
public:
  const exprt &lhs() const
  {
    return op0();
  }

  const exprt &rhs() const
  {
    return op1();
  }
};

inline const verilog_generate_assignt &
to_verilog_generate_assign(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_generate_assign);
  validate_operands(expr, 2, "generate_assign must have 2 operands");
  return static_cast<const verilog_generate_assignt &>(expr);
}

inline verilog_generate_assignt &to_verilog_generate_assign(exprt &expr)
{
  PRECONDITION(expr.id() == ID_generate_assign);
  validate_operands(expr, 2, "generate_assign must have 2 operands");
  return static_cast<verilog_generate_assignt &>(expr);
}

class verilog_generate_blockt : public verilog_module_itemt
{
public:
  explicit verilog_generate_blockt(
    verilog_module_exprt::module_itemst _module_items)
    : verilog_module_itemt(ID_generate_block)
  {
    module_items() = std::move(_module_items);
  }

  verilog_generate_blockt(
    irep_idt _base_name,
    verilog_module_exprt::module_itemst _module_items)
    : verilog_module_itemt(ID_generate_block)
  {
    set(ID_base_name, _base_name);
    module_items() = std::move(_module_items);
  }

  const irep_idt &base_name() const
  {
    return get(ID_base_name);
  }

  void base_name(irep_idt __base_name)
  {
    return set(ID_base_name, __base_name);
  }

  bool is_named() const
  {
    return !base_name().empty();
  }

  const verilog_module_exprt::module_itemst &module_items() const
  {
    return (const verilog_module_exprt::module_itemst &)operands();
  }

  verilog_module_exprt::module_itemst &module_items()
  {
    return (verilog_module_exprt::module_itemst &)operands();
  }
};

inline const verilog_generate_blockt &
to_verilog_generate_block(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_generate_block);
  return static_cast<const verilog_generate_blockt &>(expr);
}

inline verilog_generate_blockt &to_verilog_generate_block(exprt &expr)
{
  PRECONDITION(expr.id() == ID_generate_block);
  return static_cast<verilog_generate_blockt &>(expr);
}

class verilog_generate_caset : public verilog_module_itemt
{
public:
};

inline const verilog_generate_caset &to_verilog_generate_case(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_generate_case);
  return static_cast<const verilog_generate_caset &>(expr);
}

inline verilog_generate_caset &to_verilog_generate_case(exprt &expr)
{
  PRECONDITION(expr.id() == ID_generate_case);
  return static_cast<verilog_generate_caset &>(expr);
}

class verilog_generate_ift : public verilog_module_itemt
{
public:
  verilog_generate_ift() : verilog_module_itemt(ID_generate_if)
  {
  }

  const verilog_module_itemt &then_case() const
  {
    return static_cast<const verilog_module_itemt &>(get_sub()[1]);
  }

  bool has_else_case() const
  {
    return get_sub().size() == 3;
  }

  const verilog_module_itemt &else_case() const
  {
    PRECONDITION(has_else_case());
    return static_cast<const verilog_module_itemt &>(get_sub()[2]);
  }
};

inline const verilog_generate_ift &to_verilog_generate_if(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_generate_if);
  return static_cast<const verilog_generate_ift &>(expr);
}

inline verilog_generate_ift &to_verilog_generate_if(exprt &expr)
{
  PRECONDITION(expr.id() == ID_generate_if);
  return static_cast<verilog_generate_ift &>(expr);
}

class verilog_generate_fort : public verilog_module_itemt
{
public:
  verilog_generate_fort() : verilog_module_itemt(ID_generate_for)
  {
  }

  const verilog_generate_assignt &init() const
  {
    return static_cast<const verilog_generate_assignt &>(op0());
  }

  const exprt &cond() const
  {
    return op1();
  }

  const verilog_generate_assignt &increment() const
  {
    return static_cast<const verilog_generate_assignt &>(op2());
  }

  const verilog_module_itemt &body() const
  {
    return static_cast<const verilog_module_itemt &>(get_sub()[3]);
  }
};

inline const verilog_generate_fort &to_verilog_generate_for(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_generate_for);
  validate_operands(expr, 4, "generate_for must have 4 operands");
  return static_cast<const verilog_generate_fort &>(expr);
}

inline verilog_generate_fort &to_verilog_generate_for(exprt &expr)
{
  PRECONDITION(expr.id() == ID_generate_for);
  validate_operands(expr, 4, "generate_for must have 4 operands");
  return static_cast<verilog_generate_fort &>(expr);
}

class verilog_set_genvarst : public verilog_module_itemt
{
public:
  explicit verilog_set_genvarst(verilog_module_itemt _module_item)
    : verilog_module_itemt(ID_set_genvars)
  {
    add_to_operands(std::move(_module_item));
  }

  named_subt &variables()
  {
    return add(ID_variables).get_named_sub();
  }

  const named_subt &variables() const
  {
    return find(ID_variables).get_named_sub();
  }

  const verilog_module_itemt &module_item() const
  {
    return static_cast<const verilog_module_itemt &>(get_sub()[0]);
  }
};

inline const verilog_set_genvarst &to_verilog_set_genvars(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_set_genvars);
  return static_cast<const verilog_set_genvarst &>(expr);
}

inline verilog_set_genvarst &to_verilog_set_genvars(exprt &expr)
{
  PRECONDITION(expr.id() == ID_set_genvars);
  return static_cast<verilog_set_genvarst &>(expr);
}

// This class is used for all declarators in the parse tree
class verilog_declaratort : public exprt
{
public:
  const irep_idt &identifier() const
  {
    return get(ID_identifier);
  }

  void identifier(irep_idt _identifier)
  {
    set(ID_identifier, _identifier);
  }

  const irep_idt &base_name() const
  {
    return get(ID_base_name);
  }

  const exprt &value() const
  {
    return static_cast<const exprt &>(find(ID_value));
  }

  exprt &value()
  {
    return static_cast<exprt &>(add(ID_value));
  }

  bool has_value() const
  {
    return find(ID_value).is_not_nil();
  }

  // helper to generate a symbol expression
  symbol_exprt symbol_expr() const
  {
    return symbol_exprt(identifier(), type())
      .with_source_location<symbol_exprt>(*this);
  }

  // Helper to merge the declarator's unpacked array type
  // with the declaration type.
  typet merged_type(const typet &declaration_type) const;
};

using verilog_declaratorst = std::vector<verilog_declaratort>;

class verilog_parameter_declt : public verilog_module_itemt
{
public:
  inline verilog_parameter_declt() : verilog_module_itemt(ID_parameter_decl)
  {
  }

  using declaratort = verilog_declaratort;
  using declaratorst = verilog_declaratorst;

  const declaratorst &declarations() const
  {
    return (const declaratorst &)operands();
  }

  declaratorst &declarations()
  {
    return (declaratorst &)operands();
  }
};

inline const verilog_parameter_declt &
to_verilog_parameter_decl(const irept &irep)
{
  PRECONDITION(irep.id() == ID_parameter_decl);
  return static_cast<const verilog_parameter_declt &>(irep);
}

inline verilog_parameter_declt &to_verilog_parameter_decl(irept &irep)
{
  PRECONDITION(irep.id() == ID_parameter_decl);
  return static_cast<verilog_parameter_declt &>(irep);
}

class verilog_local_parameter_declt : public verilog_module_itemt
{
public:
  inline verilog_local_parameter_declt()
    : verilog_module_itemt(ID_local_parameter_decl)
  {
  }

  using declaratort = verilog_declaratort;
  using declaratorst = verilog_declaratorst;

  const declaratorst &declarations() const
  {
    return (const declaratorst &)operands();
  }

  declaratorst &declarations()
  {
    return (declaratorst &)operands();
  }
};

inline const verilog_local_parameter_declt &
to_verilog_local_parameter_decl(const irept &irep)
{
  PRECONDITION(irep.id() == ID_local_parameter_decl);
  return static_cast<const verilog_local_parameter_declt &>(irep);
}

inline verilog_local_parameter_declt &
to_verilog_local_parameter_decl(irept &irep)
{
  PRECONDITION(irep.id() == ID_local_parameter_decl);
  return static_cast<verilog_local_parameter_declt &>(irep);
}

class verilog_lett : public verilog_module_itemt
{
public:
  // These have a single declarator.
  using declaratort = verilog_declaratort;

  const declaratort &declarator() const
  {
    return static_cast<const declaratort &>(op0());
  }
};

inline const verilog_lett &to_verilog_let(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_verilog_let);
  validate_operands(expr, 1, "verilog_let must have 1 operand");
  return static_cast<const verilog_lett &>(expr);
}

inline verilog_lett &to_verilog_let(exprt &expr)
{
  PRECONDITION(expr.id() == ID_verilog_let);
  validate_operands(expr, 1, "verilog_let must have 1 operand");
  return static_cast<verilog_lett &>(expr);
}

class verilog_inst_baset : public verilog_module_itemt
{
public:
  verilog_inst_baset(irep_idt id) : verilog_module_itemt(id)
  {
  }

  irep_idt get_module() const
  {
    return get(ID_module);
  }

  void set_module(const irep_idt &module)
  {
    return set(ID_module, module);
  }

  class instancet : public exprt
  {
  public:
    const irep_idt &base_name() const
    {
      return get(ID_base_name);
    }

    const irep_idt &identifier() const
    {
      return get(ID_identifier);
    }

    void identifier(irep_idt _identifier)
    {
      return set(ID_identifier, _identifier);
    }

    const exprt::operandst &connections() const
    {
      return operands();
    }

  protected:
    using exprt::operands;
  };

  using instancest = std::vector<instancet>;

  const instancest &instances() const
  {
    return (const instancest &)(operands());
  }

  instancest &instances()
  {
    return (instancest &)(operands());
  }

protected:
  using exprt::operands;
};

class verilog_instt : public verilog_inst_baset
{
public:
  inline verilog_instt() : verilog_inst_baset(ID_inst)
  {
  }

  exprt::operandst &parameter_assignments()
  {
    return static_cast<exprt &>(add(ID_parameter_assignments)).operands();
  }

  const exprt::operandst &parameter_assignments() const
  {
    return static_cast<const exprt &>(find(ID_parameter_assignments))
      .operands();
  }
};

inline const verilog_instt &to_verilog_inst(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_inst);
  return static_cast<const verilog_instt &>(expr);
}

inline verilog_instt &to_verilog_inst(exprt &expr)
{
  PRECONDITION(expr.id() == ID_inst);
  return static_cast<verilog_instt &>(expr);
}

class verilog_inst_builtint : public verilog_inst_baset
{
public:
  inline verilog_inst_builtint() : verilog_inst_baset(ID_inst_builtin)
  {
  }
};

inline const verilog_inst_builtint &to_verilog_inst_builtin(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_inst_builtin);
  return static_cast<const verilog_inst_builtint &>(expr);
}

inline verilog_inst_builtint &to_verilog_inst_builtin(exprt &expr)
{
  PRECONDITION(expr.id() == ID_inst_builtin);
  return static_cast<verilog_inst_builtint &>(expr);
}

/// SystemVerilog has always, always_comb, always_ff and always_latch
class verilog_always_baset : public verilog_statementt
{
public:
  verilog_always_baset(
    irep_idt id,
    verilog_statementt __statement,
    source_locationt __source_location)
    : verilog_statementt(
        id,
        {std::move(__statement)},
        std::move(__source_location))
  {
  }

  verilog_statementt &statement()
  {
    return static_cast<verilog_statementt &>(op0());
  }

  const verilog_statementt &statement() const
  {
    return static_cast<const verilog_statementt &>(op0());
  }
};

inline const verilog_always_baset &to_verilog_always_base(const exprt &expr)
{
  unary_exprt::check(expr);
  return static_cast<const verilog_always_baset &>(expr);
}

inline verilog_always_baset &to_verilog_always_base(exprt &expr)
{
  unary_exprt::check(expr);
  return static_cast<verilog_always_baset &>(expr);
}

class verilog_declt:public verilog_statementt
{
public:
  verilog_declt():verilog_statementt(ID_decl)
  {
  }

  irep_idt get_class() const
  {
    return get(ID_class);
  }

  void set_class(const irep_idt &_class)
  {
    set(ID_class, _class);
  }

  // When it's not a function or task, there are declarators.
  using declaratort = verilog_declaratort;
  using declaratorst = verilog_declaratorst;

  declaratorst &declarators()
  {
    return (declaratorst &)operands();
  }

  const declaratorst &declarators() const
  {
    return (const declaratorst &)operands();
  }

  // Function and task declarations have:
  // a) an identifier,
  // b) an optional list of ANSI-style ports,
  // c) further declarations,
  // d) a body.
  irep_idt get_identifier() const
  {
    return find(ID_symbol).get(ID_identifier);
  }

  void set_identifier(const irep_idt &identifier)
  {
    add(ID_symbol).set(ID_identifier, identifier);
  }

  using portst = std::vector<verilog_declt>;

  portst &ports()
  {
    return (portst &)(add(ID_ports).get_sub());
  }

  const portst &ports() const
  {
    return (const portst &)(find(ID_ports).get_sub());
  }

  using declarationst = std::vector<verilog_declt>;

  declarationst &declarations()
  {
    return (declarationst &)(add("declarations").get_sub());
  }

  const declarationst &declarations() const
  {
    return (const declarationst &)(find("declarations").get_sub());
  }

  verilog_statementt &body()
  {
    return static_cast<verilog_statementt &>(add(ID_body));
  }

  const verilog_statementt &body() const
  {
    return static_cast<const verilog_statementt &>(find(ID_body));
  }
};

inline const verilog_declt &to_verilog_decl(const irept &irep)
{
  PRECONDITION(irep.id() == ID_decl);
  return static_cast<const verilog_declt &>(irep);
}

inline verilog_declt &to_verilog_decl(exprt &irep)
{
  PRECONDITION(irep.id() == ID_decl);
  return static_cast<verilog_declt &>(irep);
}

class verilog_initialt:public verilog_statementt
{
public:
  verilog_initialt():verilog_statementt(ID_initial)
  {
    operands().resize(1);
  }

  verilog_statementt &statement()
  {
    return static_cast<verilog_statementt &>(op0());
  }

  const verilog_statementt &statement() const
  {
    return static_cast<const verilog_statementt &>(op0());
  }
};

inline const verilog_initialt &to_verilog_initial(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_initial);
  PRECONDITION(expr.operands().size() == 1);
  return static_cast<const verilog_initialt &>(expr);
}

inline verilog_initialt &to_verilog_initial(exprt &expr)
{
  PRECONDITION(expr.id() == ID_initial);
  PRECONDITION(expr.operands().size() == 1);
  return static_cast<verilog_initialt &>(expr);
}

class verilog_label_statementt : public verilog_statementt
{
public:
  verilog_label_statementt() : verilog_statementt(ID_verilog_label_statement)
  {
    operands().resize(1);
  }

  const irep_idt &label() const
  {
    return get(ID_base_name);
  }

  verilog_statementt &statement()
  {
    return static_cast<verilog_statementt &>(op0());
  }

  const verilog_statementt &statement() const
  {
    return static_cast<const verilog_statementt &>(op0());
  }
};

inline const verilog_label_statementt &
to_verilog_label_statement(const verilog_statementt &statement)
{
  PRECONDITION(statement.id() == ID_verilog_label_statement);
  unary_exprt::check(statement);
  return static_cast<const verilog_label_statementt &>(statement);
}

inline verilog_label_statementt &
to_verilog_label_statement(verilog_statementt &statement)
{
  PRECONDITION(statement.id() == ID_verilog_label_statement);
  unary_exprt::check(statement);
  return static_cast<verilog_label_statementt &>(statement);
}

class verilog_blockt:public verilog_statementt
{
public:
  verilog_blockt():verilog_statementt(ID_block)
  {
  }

  using statementst = std::vector<verilog_statementt>;

  statementst &statements()
  {
    return (statementst &)operands();
  }

  const statementst &statements() const
  {
    return (const statementst &)operands();
  }

  irep_idt base_name() const
  {
    return get(ID_base_name);
  }

  bool is_named() const
  {
    return !get(ID_base_name).empty();
  }
};

inline const verilog_blockt &to_verilog_block(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_block);
  return static_cast<const verilog_blockt &>(expr);
}

inline verilog_blockt &to_verilog_block(exprt &expr)
{
  PRECONDITION(expr.id() == ID_block);
  return static_cast<verilog_blockt &>(expr);
}

class verilog_case_baset:public verilog_statementt
{
public:
  verilog_case_baset()
  {
  }
  
  explicit verilog_case_baset(const irep_idt &_id):verilog_statementt(_id)
  {
  }
  
  inline exprt &case_operand()
  {
    return op0();
  }

  inline const exprt &case_operand() const
  {
    return op0();
  }
};

inline const verilog_case_baset &to_verilog_case_base(const exprt &expr)
{
  return static_cast<const verilog_case_baset &>(expr);
}

inline verilog_case_baset &to_verilog_case_base(exprt &expr)
{
  return static_cast<verilog_case_baset &>(expr);
}

class verilog_case_itemt:public exprt
{
public:
  verilog_case_itemt():exprt("case_item")
  {
    operands().resize(2);
  }
  
  inline exprt &case_value()
  {
    return op0();
  }

  inline const exprt &case_value() const
  {
    return op0();
  }

  inline verilog_statementt &case_statement()
  {
    return to_verilog_statement(op1());
  }

  inline const verilog_statementt &case_statement() const
  {
    return to_verilog_statement(op1());
  }
};

inline const verilog_case_itemt &to_verilog_case_item(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_case_item);
  binary_exprt::check(expr);
  return static_cast<const verilog_case_itemt &>(expr);
}

inline verilog_case_itemt &to_verilog_case_item(exprt &expr)
{
  PRECONDITION(expr.id() == ID_case_item);
  binary_exprt::check(expr);
  return static_cast<verilog_case_itemt &>(expr);
}

class verilog_caset:public verilog_case_baset
{
public:
  verilog_caset():verilog_case_baset(ID_case)
  {
  }
};

inline const verilog_caset &to_verilog_case(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_case && expr.operands().size() >= 1);
  return static_cast<const verilog_caset &>(expr);
}

inline verilog_caset &to_verilog_case(exprt &expr)
{
  PRECONDITION(expr.id() == ID_case && expr.operands().size() >= 1);
  return static_cast<verilog_caset &>(expr);
}

class verilog_ift:public verilog_statementt
{
public:
  verilog_ift(exprt __cond, verilog_statementt __then_case)
    : verilog_statementt(ID_if)
  {
    add_to_operands(std::move(__cond), std::move(__then_case));
  }

  verilog_ift(
    exprt __cond,
    verilog_statementt __then_case,
    verilog_statementt __else_case)
    : verilog_statementt(ID_if)
  {
    add_to_operands(
      std::move(__cond), std::move(__then_case), std::move(__else_case));
  }

  exprt &cond()
  {
    return op0();
  }

  const exprt &cond() const
  {
    return op0();
  }

  verilog_statementt &then_case()
  {
    return static_cast<verilog_statementt &>(op1());
  }

  const verilog_statementt &then_case() const
  {
    return static_cast<const verilog_statementt &>(op1());
  }

  bool has_else_case() const
  {
    return operands().size() == 3;
  }

  verilog_statementt &else_case()
  {
    return static_cast<verilog_statementt &>(op2());
  }

  const verilog_statementt &else_case() const
  {
    return static_cast<const verilog_statementt &>(op2());
  }
};

inline const verilog_ift &to_verilog_if(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_if);
  DATA_INVARIANT(
    expr.operands().size() == 2 || expr.operands().size() == 3,
    "if has two or three operands");
  return static_cast<const verilog_ift &>(expr);
}

inline verilog_ift &to_verilog_if(exprt &expr)
{
  PRECONDITION(expr.id() == ID_if);
  DATA_INVARIANT(
    expr.operands().size() == 2 || expr.operands().size() == 3,
    "if has two or three operands");
  return static_cast<verilog_ift &>(expr);
}

class verilog_function_callt:public verilog_statementt
{
public:
  verilog_function_callt():verilog_statementt(ID_function_call)
  {
    operands().resize(2);
  }

  exprt &function()
  {
    return op0();
  }

  const exprt &function() const
  {
    return op0();
  }
  
  exprt::operandst &arguments()
  {
    return op1().operands();
  }

  const exprt::operandst &arguments() const
  {
    return op1().operands();
  }
};

inline const verilog_function_callt &to_verilog_function_call(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_function_call);
  binary_exprt::check(expr);
  return static_cast<const verilog_function_callt &>(expr);
}

inline verilog_function_callt &to_verilog_function_call(exprt &expr)
{
  PRECONDITION(expr.id() == ID_function_call);
  binary_exprt::check(expr);
  return static_cast<verilog_function_callt &>(expr);
}

class verilog_event_guardt:public verilog_statementt
{
public:
  verilog_event_guardt():verilog_statementt(ID_event_guard)
  {
    operands().resize(2);
  }

  exprt &guard()
  {
    return op0();
  }

  const exprt &guard() const
  {
    return op0();
  }
  
  verilog_statementt &body()
  {
    return static_cast<verilog_statementt &>(op1());
  }

  const verilog_statementt &body() const
  {
    return static_cast<const verilog_statementt &>(op1());
  }
};

inline const verilog_event_guardt &to_verilog_event_guard(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_event_guard);
  binary_exprt::check(expr);
  return static_cast<const verilog_event_guardt &>(expr);
}

inline verilog_event_guardt &to_verilog_event_guard(exprt &expr)
{
  PRECONDITION(expr.id() == ID_event_guard);
  binary_exprt::check(expr);
  return static_cast<verilog_event_guardt &>(expr);
}

class verilog_delayt:public verilog_statementt
{
public:
  verilog_delayt():verilog_statementt(ID_delay)
  {
    operands().resize(2);
  }
  
  verilog_statementt &body()
  {
    return static_cast<verilog_statementt &>(op1());
  }

  const verilog_statementt &body() const
  {
    return static_cast<const verilog_statementt &>(op1());
  }
};

inline const verilog_delayt &to_verilog_delay(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_delay);
  binary_exprt::check(expr);
  return static_cast<const verilog_delayt &>(expr);
}

inline verilog_delayt &to_verilog_delay(exprt &expr)
{
  PRECONDITION(expr.id() == ID_delay);
  binary_exprt::check(expr);
  return static_cast<verilog_delayt &>(expr);
}

class verilog_fort:public verilog_statementt
{
public:
  verilog_fort():verilog_statementt(ID_for)
  {
    operands().resize(4);
  }
  
  verilog_statementt &initialization()
  {
    return static_cast<verilog_statementt &>(op0());
  }

  const verilog_statementt &initialization() const
  {
    return static_cast<const verilog_statementt &>(op0());
  }
  
  exprt &condition()
  {
    return op1();
  }

  const exprt &condition() const
  {
    return op1();
  }
  
  verilog_statementt &inc_statement()
  {
    return static_cast<verilog_statementt &>(op2());
  }

  const verilog_statementt &inc_statement() const
  {
    return static_cast<const verilog_statementt &>(op2());
  }
  
  verilog_statementt &body()
  {
    return static_cast<verilog_statementt &>(op3());
  }

  const verilog_statementt &body() const
  {
    return static_cast<const verilog_statementt &>(op3());
  }
};

inline const verilog_fort &to_verilog_for(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_for && expr.operands().size() == 4);
  return static_cast<const verilog_fort &>(expr);
}

inline verilog_fort &to_verilog_for(exprt &expr)
{
  PRECONDITION(expr.id() == ID_for && expr.operands().size() == 4);
  return static_cast<verilog_fort &>(expr);
}

class verilog_forevert:public verilog_statementt
{
public:
  verilog_forevert():verilog_statementt(ID_forever)
  {
  }

  verilog_statementt &body()
  {
    return static_cast<verilog_statementt &>(op0());
  }

  const verilog_statementt &body() const
  {
    return static_cast<const verilog_statementt &>(op0());
  }
};

inline const verilog_forevert &to_verilog_forever(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_forever);
  PRECONDITION(expr.operands().size() == 1);
  return static_cast<const verilog_forevert &>(expr);
}

inline verilog_forevert &to_verilog_forever(exprt &expr)
{
  PRECONDITION(expr.id() == ID_forever);
  PRECONDITION(expr.operands().size() == 1);
  return static_cast<verilog_forevert &>(expr);
}

class verilog_whilet:public verilog_statementt
{
public:
  verilog_whilet():verilog_statementt(ID_while)
  {
    operands().resize(2);
  }
  
  exprt &condition()
  {
    return op0();
  }

  const exprt &condition() const
  {
    return op0();
  }
  
  verilog_statementt &body()
  {
    return static_cast<verilog_statementt &>(op1());
  }

  const verilog_statementt &body() const
  {
    return static_cast<const verilog_statementt &>(op1());
  }
};

inline const verilog_whilet &to_verilog_while(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_while);
  binary_exprt::check(expr);
  return static_cast<const verilog_whilet &>(expr);
}

inline verilog_whilet &to_verilog_while(exprt &expr)
{
  PRECONDITION(expr.id() == ID_while);
  binary_exprt::check(expr);
  return static_cast<verilog_whilet &>(expr);
}

class verilog_repeatt:public verilog_statementt
{
public:
  verilog_repeatt():verilog_statementt(ID_repeat)
  {
    operands().resize(2);
  }

  exprt &condition()
  {
    return op0();
  }

  const exprt &condition() const
  {
    return op0();
  }
  
  verilog_statementt &body()
  {
    return static_cast<verilog_statementt &>(op1());
  }

  const verilog_statementt &body() const
  {
    return static_cast<const verilog_statementt &>(op1());
  }
};

inline const verilog_repeatt &to_verilog_repeat(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_repeat);
  binary_exprt::check(expr);
  return static_cast<const verilog_repeatt &>(expr);
}

inline verilog_repeatt &to_verilog_repeat(exprt &expr)
{
  PRECONDITION(expr.id() == ID_repeat);
  binary_exprt::check(expr);
  return static_cast<verilog_repeatt &>(expr);
}

class verilog_procedural_continuous_assignt:public verilog_statementt
{
public:
  verilog_procedural_continuous_assignt():verilog_statementt(ID_continuous_assign)
  {
  }
};

inline const verilog_procedural_continuous_assignt &
to_verilog_procedural_continuous_assign(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_continuous_assign);
  return static_cast<const verilog_procedural_continuous_assignt &>(expr);
}

inline verilog_procedural_continuous_assignt &
to_verilog_procedural_continuous_assign(exprt &expr)
{
  PRECONDITION(expr.id() == ID_continuous_assign);
  return static_cast<verilog_procedural_continuous_assignt &>(expr);
}

class verilog_forcet:public verilog_statementt
{
public:
  verilog_forcet():verilog_statementt(ID_force)
  {
    operands().resize(2);
  }

  verilog_forcet(exprt _lhs, exprt _rhs)
    : verilog_statementt(ID_force, {std::move(_lhs), std::move(_rhs)})
  {
  }

  const exprt &lhs() const
  {
    return op0();
  }

  const exprt &rhs() const
  {
    return op1();
  }
  
  exprt &lhs()
  {
    return op0();
  }

  exprt &rhs()
  {
    return op1();
  }
};

inline const verilog_forcet &to_verilog_force(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_force);
  binary_exprt::check(expr);
  return static_cast<const verilog_forcet &>(expr);
}

inline verilog_forcet &to_verilog_force(exprt &expr)
{
  PRECONDITION(expr.id() == ID_force);
  binary_exprt::check(expr);
  return static_cast<verilog_forcet &>(expr);
}

class verilog_continuous_assignt:public verilog_module_itemt
{
public:
  explicit verilog_continuous_assignt(equal_exprt assignment)
    : verilog_module_itemt(ID_continuous_assign)
  {
    add_to_operands(std::move(assignment));
  }
};

inline const verilog_continuous_assignt &
to_verilog_continuous_assign(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_continuous_assign);
  return static_cast<const verilog_continuous_assignt &>(expr);
}

inline verilog_continuous_assignt &to_verilog_continuous_assign(exprt &expr)
{
  PRECONDITION(expr.id() == ID_continuous_assign);
  return static_cast<verilog_continuous_assignt &>(expr);
}

class verilog_parameter_overridet : public verilog_module_itemt
{
public:
  verilog_parameter_overridet() : verilog_module_itemt(ID_parameter_override)
  {
  }

  exprt::operandst &assignments()
  {
    return operands();
  }

  const exprt::operandst &assignments() const
  {
    return operands();
  }
};

inline const verilog_parameter_overridet &
to_verilog_parameter_override(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_parameter_override);
  return static_cast<const verilog_parameter_overridet &>(expr);
}

inline verilog_parameter_overridet &to_verilog_parameter_override(exprt &expr)
{
  PRECONDITION(expr.id() == ID_parameter_override);
  return static_cast<verilog_parameter_overridet &>(expr);
}

class verilog_assignt:public verilog_statementt
{
public:
  // both blocking and non-blocking
  inline verilog_assignt()
  {
    operands().resize(2);
  }

  inline verilog_assignt(const irep_idt &_id):verilog_statementt(_id)
  {
    operands().resize(2);
  }

  inline verilog_assignt(const irep_idt &_id, exprt _lhs, exprt _rhs)
    : verilog_statementt(_id)
  {
    add_to_operands(std::move(_lhs), std::move(_rhs));
  }
  
  inline const exprt &lhs() const
  {
    return op0();
  }

  inline const exprt &rhs() const
  {
    return op1();
  }
  
  inline exprt &lhs()
  {
    return op0();
  }

  inline exprt &rhs()
  {
    return op1();
  }
};

inline const verilog_assignt &to_verilog_assign(const exprt &expr)
{
  return static_cast<const verilog_assignt &>(expr);
}

inline verilog_assignt &to_verilog_assign(exprt &expr)
{
  return static_cast<verilog_assignt &>(expr);
}

class verilog_blocking_assignt:public verilog_assignt
{
public:
  verilog_blocking_assignt():verilog_assignt(ID_blocking_assign)
  {
  }

  verilog_blocking_assignt(
    const exprt &_lhs, const exprt &_rhs):
    verilog_assignt(ID_blocking_assign, _lhs, _rhs)
  {
  }
};

inline const verilog_blocking_assignt &
to_verilog_blocking_assign(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_blocking_assign);
  return static_cast<const verilog_blocking_assignt &>(expr);
}

inline verilog_blocking_assignt &to_verilog_blocking_assign(exprt &expr)
{
  PRECONDITION(expr.id() == ID_blocking_assign);
  return static_cast<verilog_blocking_assignt &>(expr);
}

class verilog_non_blocking_assignt:public verilog_assignt
{
public:
  verilog_non_blocking_assignt():verilog_assignt(ID_non_blocking_assign)
  {
  }
};

inline const verilog_non_blocking_assignt &
to_verilog_non_blocking_assign(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_non_blocking_assign);
  return static_cast<const verilog_non_blocking_assignt &>(expr);
}

inline verilog_non_blocking_assignt &to_verilog_non_blocking_assign(exprt &expr)
{
  PRECONDITION(expr.id() == ID_non_blocking_assign);
  return static_cast<verilog_non_blocking_assignt &>(expr);
}

/// Verilog concurrent assertion module item
class verilog_assert_module_itemt : public verilog_module_itemt
{
public:
  verilog_assert_module_itemt()
    : verilog_module_itemt(ID_verilog_assert_property)
  {
    operands().resize(2);
  }
  
  inline exprt &condition()
  {
    return op0();
  }

  inline const exprt &condition() const
  {
    return op0();
  }

  const irep_idt &identifier() const
  {
    return get(ID_identifier);
  }

  void identifier(irep_idt __identifier)
  {
    set(ID_identifier, __identifier);
  }
};

inline const verilog_assert_module_itemt &
to_verilog_assert_module_item(const verilog_module_itemt &module_item)
{
  PRECONDITION(module_item.id() == ID_verilog_assert_property);
  binary_exprt::check(module_item);
  return static_cast<const verilog_assert_module_itemt &>(module_item);
}

inline verilog_assert_module_itemt &
to_verilog_assert_module_item(verilog_module_itemt &module_item)
{
  PRECONDITION(module_item.id() == ID_verilog_assert_property);
  binary_exprt::check(module_item);
  return static_cast<verilog_assert_module_itemt &>(module_item);
}

/// Verilog concurrent assumption module item
class verilog_assume_module_itemt : public verilog_module_itemt
{
public:
  verilog_assume_module_itemt()
    : verilog_module_itemt(ID_verilog_assume_property)
  {
    operands().resize(2);
  }

  inline exprt &condition()
  {
    return op0();
  }

  inline const exprt &condition() const
  {
    return op0();
  }

  const irep_idt &identifier() const
  {
    return get(ID_identifier);
  }

  void identifier(irep_idt __identifier)
  {
    set(ID_identifier, __identifier);
  }
};

inline const verilog_assume_module_itemt &
to_verilog_assume_module_item(const verilog_module_itemt &module_item)
{
  PRECONDITION(module_item.id() == ID_verilog_assume_property);
  binary_exprt::check(module_item);
  return static_cast<const verilog_assume_module_itemt &>(module_item);
}

inline verilog_assume_module_itemt &
to_verilog_assume_module_item(verilog_module_itemt &module_item)
{
  PRECONDITION(module_item.id() == ID_verilog_assume_property);
  binary_exprt::check(module_item);
  return static_cast<verilog_assume_module_itemt &>(module_item);
}

// Can be one of three:
// 1) Intermediate assertion statement
// 2) Concurrent assertion statement
// 3) SMV-style assertion statement
class verilog_assert_statementt : public verilog_statementt
{
public:
  verilog_assert_statementt() : verilog_statementt(ID_assert)
  {
    operands().resize(2);
  }

  inline exprt &condition()
  {
    return op0();
  }

  inline const exprt &condition() const
  {
    return op0();
  }

  // The Verilog intermediate assertion does not have an identifier,
  // but the SMV-style ones do.
  const irep_idt &identifier() const
  {
    return get(ID_identifier);
  }

  void identifier(irep_idt _identifier)
  {
    set(ID_identifier, _identifier);
  }
};

inline const verilog_assert_statementt &
to_verilog_assert_statement(const verilog_statementt &statement)
{
  PRECONDITION(
    statement.id() == ID_assert ||
    statement.id() == ID_verilog_assert_property ||
    statement.id() == ID_verilog_smv_assert);
  binary_exprt::check(statement);
  return static_cast<const verilog_assert_statementt &>(statement);
}

inline verilog_assert_statementt &
to_verilog_assert_statement(verilog_statementt &statement)
{
  PRECONDITION(
    statement.id() == ID_assert ||
    statement.id() == ID_verilog_assert_property ||
    statement.id() == ID_verilog_smv_assert);
  binary_exprt::check(statement);
  return static_cast<verilog_assert_statementt &>(statement);
}

// Can be one of three:
// 1) Intermediate assumption statement
// 2) Concurrent assumption statement
// 3) SMV-style assumption statement
class verilog_assume_statementt : public verilog_statementt
{
public:
  verilog_assume_statementt() : verilog_statementt(ID_assume)
  {
    operands().resize(2);
  }

  inline exprt &condition()
  {
    return op0();
  }

  inline const exprt &condition() const
  {
    return op0();
  }

  // The Verilog intermediate assumption does not have an identifier,
  // but the SMV-style ones do.
  const irep_idt &identifier() const
  {
    return get(ID_identifier);
  }

  void identifier(irep_idt _identifier)
  {
    set(ID_identifier, _identifier);
  }
};

inline const verilog_assume_statementt &
to_verilog_assume_statement(const verilog_statementt &statement)
{
  PRECONDITION(
    statement.id() == ID_assume ||
    statement.id() == ID_verilog_assume_property ||
    statement.id() == ID_verilog_smv_assume);
  binary_exprt::check(statement);
  return static_cast<const verilog_assume_statementt &>(statement);
}

inline verilog_assume_statementt &
to_verilog_assume_statement(verilog_statementt &statement)
{
  PRECONDITION(
    statement.id() == ID_assume ||
    statement.id() == ID_verilog_assume_property ||
    statement.id() == ID_verilog_smv_assume);
  binary_exprt::check(statement);
  return static_cast<verilog_assume_statementt &>(statement);
}

class verilog_module_sourcet : public irept
{
public:
  irep_idt name() const
  {
    return get(ID_name);
  }

  using parameter_port_listt = verilog_parameter_declt::declaratorst;

  const parameter_port_listt &parameter_port_list() const
  {
    return (
      const parameter_port_listt &)(find(ID_parameter_port_list).get_sub());
  }

  parameter_port_listt &parameter_port_list()
  {
    return (parameter_port_listt &)(add(ID_parameter_port_list).get_sub());
  }

  using port_listt = std::vector<verilog_declt>;

  const port_listt &ports() const
  {
    return (const port_listt &)(find(ID_ports).get_sub());
  }

  using module_itemst = std::vector<class verilog_module_itemt>;

  const module_itemst &module_items() const
  {
    return (const module_itemst &)(find(ID_module_items).get_sub());
  }

  module_itemst &module_items()
  {
    return (module_itemst &)(add(ID_module_items).get_sub());
  }

  const source_locationt &source_location()
  {
    return static_cast<const source_locationt &>(find(ID_C_source_location));
  }
};

inline const verilog_module_sourcet &to_verilog_module_source(const irept &irep)
{
  return static_cast<const verilog_module_sourcet &>(irep);
}

inline verilog_module_sourcet &to_verilog_module_source(irept &irep)
{
  return static_cast<verilog_module_sourcet &>(irep);
}

#endif
