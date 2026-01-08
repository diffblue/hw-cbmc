/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_VERILOG_EXPR_H
#define CPROVER_VERILOG_EXPR_H

#include <util/std_expr.h>

#include <set>

/// A simple Verilog identifier, unqualified
class verilog_identifier_exprt : public nullary_exprt
{
public:
  const irep_idt &base_name() const
  {
    return get(ID_base_name);
  }

  void identifier(irep_idt _base_name)
  {
    set(ID_base_name, _base_name);
  }
};

inline const verilog_identifier_exprt &
to_verilog_identifier_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_verilog_identifier);
  verilog_identifier_exprt::check(expr);
  return static_cast<const verilog_identifier_exprt &>(expr);
}

inline verilog_identifier_exprt &to_verilog_identifier_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_verilog_identifier);
  verilog_identifier_exprt::check(expr);
  return static_cast<verilog_identifier_exprt &>(expr);
}

/// The syntax for these A.B, where A is a module identifier and B
/// is an identifier within that module. B is given als symbol_exprt.
class hierarchical_identifier_exprt : public binary_exprt
{
public:
  const exprt &module() const
  {
    return op0();
  }

  const verilog_identifier_exprt &item() const
  {
    return static_cast<const verilog_identifier_exprt &>(binary_exprt::op1());
  }

  const verilog_identifier_exprt &rhs() const
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

/// ==
/// returns 'x' if either operand contains x or z
class verilog_logical_equality_exprt : public equal_exprt
{
public:
};

inline const verilog_logical_equality_exprt &
to_verilog_logical_equality_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_verilog_logical_equality);
  binary_exprt::check(expr);
  return static_cast<const verilog_logical_equality_exprt &>(expr);
}

inline verilog_logical_equality_exprt &
to_verilog_logical_equality_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_verilog_logical_equality);
  binary_exprt::check(expr);
  return static_cast<verilog_logical_equality_exprt &>(expr);
}

/// !=
/// returns 'x' if either operand contains x or z
class verilog_logical_inequality_exprt : public equal_exprt
{
public:
};

inline const verilog_logical_inequality_exprt &
to_verilog_logical_inequality_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_verilog_logical_inequality);
  binary_exprt::check(expr);
  return static_cast<const verilog_logical_inequality_exprt &>(expr);
}

inline verilog_logical_inequality_exprt &
to_verilog_logical_inequality_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_verilog_logical_inequality);
  binary_exprt::check(expr);
  return static_cast<verilog_logical_inequality_exprt &>(expr);
}

/// ===
/// returns true if operands are identical
class verilog_case_equality_exprt : public binary_relation_exprt
{
public:
  verilog_case_equality_exprt(exprt lhs, exprt rhs)
    : binary_relation_exprt{
        std::move(lhs),
        ID_verilog_case_equality,
        std::move(rhs)}
  {
  }

  exprt lower() const
  {
    return equal_exprt{lhs(), rhs()};
  }
};

inline const verilog_case_equality_exprt &
to_verilog_case_equality_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_verilog_case_equality);
  verilog_case_equality_exprt::check(expr);
  return static_cast<const verilog_case_equality_exprt &>(expr);
}

inline verilog_case_equality_exprt &to_verilog_case_equality_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_verilog_case_equality);
  verilog_case_equality_exprt::check(expr);
  return static_cast<verilog_case_equality_exprt &>(expr);
}

/// !==
/// returns true if the operands are different
class verilog_case_inequality_exprt : public binary_relation_exprt
{
public:
  verilog_case_inequality_exprt(exprt lhs, exprt rhs)
    : binary_relation_exprt{
        std::move(lhs),
        ID_verilog_case_inequality,
        std::move(rhs)}
  {
  }

  exprt lower() const
  {
    return notequal_exprt{lhs(), rhs()};
  }
};

inline const verilog_case_inequality_exprt &
to_verilog_case_inequality_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_verilog_case_inequality);
  verilog_case_inequality_exprt::check(expr);
  return static_cast<const verilog_case_inequality_exprt &>(expr);
}

inline verilog_case_inequality_exprt &
to_verilog_case_inequality_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_verilog_case_inequality);
  verilog_case_inequality_exprt::check(expr);
  return static_cast<verilog_case_inequality_exprt &>(expr);
}

/// ==?
class verilog_wildcard_equality_exprt : public binary_exprt
{
public:
  verilog_wildcard_equality_exprt(exprt, exprt);
};

inline const verilog_wildcard_equality_exprt &
to_verilog_wildcard_equality_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_verilog_wildcard_equality);
  binary_exprt::check(expr);
  return static_cast<const verilog_wildcard_equality_exprt &>(expr);
}

inline verilog_wildcard_equality_exprt &
to_verilog_wildcard_equality_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_verilog_wildcard_equality);
  binary_exprt::check(expr);
  return static_cast<verilog_wildcard_equality_exprt &>(expr);
}

/// !=?
class verilog_wildcard_inequality_exprt : public equal_exprt
{
public:
};

inline const verilog_wildcard_inequality_exprt &
to_verilog_wildcard_inequality_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_verilog_wildcard_inequality);
  binary_exprt::check(expr);
  return static_cast<const verilog_wildcard_inequality_exprt &>(expr);
}

inline verilog_wildcard_inequality_exprt &
to_verilog_wildcard_inequality_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_verilog_wildcard_inequality);
  binary_exprt::check(expr);
  return static_cast<verilog_wildcard_inequality_exprt &>(expr);
}

/// <->, not to be confused with SVA iff
class verilog_iff_exprt : public binary_exprt
{
public:
  verilog_iff_exprt(exprt lhs, exprt rhs)
    : binary_exprt{std::move(lhs), ID_verilog_iff, std::move(rhs), bool_typet{}}
  {
  }
};

inline const verilog_iff_exprt &to_verilog_iff_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_verilog_iff);
  binary_exprt::check(expr);
  return static_cast<const verilog_iff_exprt &>(expr);
}

inline verilog_iff_exprt &to_verilog_iff_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_verilog_iff);
  binary_exprt::check(expr);
  return static_cast<verilog_iff_exprt &>(expr);
}

/// ->, not to be confused with SVA implies
class verilog_implies_exprt : public binary_exprt
{
public:
  verilog_implies_exprt(exprt lhs, exprt rhs)
    : binary_exprt{
        std::move(lhs),
        ID_verilog_implies,
        std::move(rhs),
        bool_typet{}}
  {
  }
};

inline const verilog_implies_exprt &to_verilog_implies_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_verilog_implies);
  verilog_implies_exprt::check(expr);
  return static_cast<const verilog_implies_exprt &>(expr);
}

inline verilog_implies_exprt &to_verilog_implies_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_verilog_implies);
  verilog_implies_exprt::check(expr);
  return static_cast<verilog_implies_exprt &>(expr);
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

  static void
  check(const exprt &expr, validation_modet vm = validation_modet::INVARIANT)
  {
    exprt::check(expr, vm);
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
  verilog_generate_assignt(exprt __lhs, exprt __rhs)
    : verilog_module_itemt{ID_generate_assign}
  {
    add_to_operands(std::move(__lhs), std::move(__rhs));
  }

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

  // assignment, ++, --
  const verilog_module_itemt &iteration() const
  {
    return static_cast<const verilog_module_itemt &>(op2());
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
    auto result = symbol_exprt(identifier(), type());
    result.with_source_location(*this);
    return result;
  }

  // Helper to merge the declarator's unpacked array type
  // with the declaration type.
  typet merged_type(const typet &declaration_type) const;
};

using verilog_declaratorst = std::vector<verilog_declaratort>;

/// a SystemVerilog parameter declaration
class verilog_parameter_declt : public verilog_module_itemt
{
public:
  inline verilog_parameter_declt() : verilog_module_itemt(ID_parameter_decl)
  {
  }

  using declaratort = verilog_declaratort;
  using declaratorst = verilog_declaratorst;

  const declaratorst &declarators() const
  {
    return (const declaratorst &)operands();
  }

  declaratorst &declarators()
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

  const declaratorst &declarators() const
  {
    return (const declaratorst &)operands();
  }

  declaratorst &declarators()
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

  class named_port_connectiont : public binary_exprt
  {
  public:
    named_port_connectiont(exprt _port, exprt _value)
      : binary_exprt(
          std::move(_port),
          ID_verilog_named_port_connection,
          std::move(_value),
          typet{})
    {
    }

    const exprt &port() const
    {
      return op0();
    }

    exprt &port()
    {
      return op0();
    }

    const exprt &value() const
    {
      return op1();
    }

    exprt &value()
    {
      return op1();
    }
  };

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

    exprt::operandst &connections()
    {
      return operands();
    }

    bool positional_port_connections() const
    {
      return !named_port_connections();
    }

    bool named_port_connections() const
    {
      auto &connections = this->connections();
      return connections.empty() ||
             (connections.front().id() == ID_verilog_named_port_connection ||
              connections.front().id() == ID_verilog_wildcard_port_connection);
    }

    const typet &instance_array() const
    {
      return static_cast<const typet &>(find(ID_verilog_instance_array));
    }

    typet &instance_array()
    {
      return static_cast<typet &>(add(ID_verilog_instance_array));
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

inline const verilog_inst_baset::named_port_connectiont &
to_verilog_named_port_connection(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_verilog_named_port_connection);
  verilog_inst_baset::named_port_connectiont::check(expr);
  return static_cast<const verilog_inst_baset::named_port_connectiont &>(expr);
}

inline verilog_inst_baset::named_port_connectiont &
to_verilog_named_port_connection(exprt &expr)
{
  PRECONDITION(expr.id() == ID_verilog_named_port_connection);
  verilog_inst_baset::named_port_connectiont::check(expr);
  return static_cast<verilog_inst_baset::named_port_connectiont &>(expr);
}

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

/// function and task declarations
class verilog_function_or_task_declt : public verilog_module_itemt
{
public:
  verilog_function_or_task_declt(irep_idt __id) : verilog_module_itemt(__id)
  {
  }

  // Function and task declarations have:
  // a) an base name and identifier,
  // b) an optional list of ANSI-style ports,
  // c) further declarations,
  // d) a body.
  irep_idt base_name() const
  {
    return find(ID_symbol).get(ID_base_name);
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
    return (declarationst &)(add(ID_verilog_declarations).get_sub());
  }

  const declarationst &declarations() const
  {
    return (const declarationst &)(find(ID_verilog_declarations).get_sub());
  }

  class bodyt : public exprt
  {
  public:
    using statementst = std::vector<verilog_statementt>;

    statementst &statements()
    {
      return (statementst &)(operands());
    }

    const statementst &statements() const
    {
      return (const statementst &)(operands());
    }
  };

  bodyt &body()
  {
    return static_cast<bodyt &>(add(ID_body));
  }

  const bodyt &body() const
  {
    return static_cast<const bodyt &>(find(ID_body));
  }
};

inline const verilog_function_or_task_declt &
to_verilog_function_or_task_decl(const irept &irep)
{
  PRECONDITION(
    irep.id() == ID_verilog_function_decl || irep.id() == ID_verilog_task_decl);
  return static_cast<const verilog_function_or_task_declt &>(irep);
}

inline verilog_function_or_task_declt &
to_verilog_function_or_task_decl(exprt &irep)
{
  PRECONDITION(
    irep.id() == ID_verilog_function_decl || irep.id() == ID_verilog_task_decl);
  return static_cast<verilog_function_or_task_declt &>(irep);
}

class verilog_initialt:public verilog_statementt
{
public:
  verilog_initialt():verilog_statementt(ID_initial)
  {
    operands().resize(1);
  }

  explicit verilog_initialt(verilog_statementt _statement)
    : verilog_statementt(ID_initial)
  {
    add_to_operands(std::move(_statement));
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

class verilog_case_itemt : public binary_exprt
{
public:
  verilog_case_itemt(exprt value, verilog_statementt statement)
    : binary_exprt(std::move(value), ID_case_item, std::move(statement))
  {
  }

  bool is_default() const
  {
    return case_value().id() == ID_default;
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

protected:
  using binary_exprt::op0;
  using binary_exprt::op1;
};

inline const verilog_case_itemt &to_verilog_case_item(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_case_item);
  verilog_case_itemt::check(expr);
  return static_cast<const verilog_case_itemt &>(expr);
}

inline verilog_case_itemt &to_verilog_case_item(exprt &expr)
{
  PRECONDITION(expr.id() == ID_case_item);
  verilog_case_itemt::check(expr);
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

/// task or function enable
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

  bool is_system_function_call() const;

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

  using statementst = std::vector<verilog_statementt>;

  statementst &initialization()
  {
    return (statementst &)(op0().operands());
  }

  const statementst &initialization() const
  {
    return (const statementst &)(op0().operands());
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

class verilog_breakt : public verilog_statementt
{
public:
  verilog_breakt() : verilog_statementt(ID_break)
  {
  }
};

inline const verilog_breakt &to_verilog_break(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_break);
  return static_cast<const verilog_breakt &>(expr);
}

inline verilog_breakt &to_verilog_break(exprt &expr)
{
  PRECONDITION(expr.id() == ID_break);
  return static_cast<verilog_breakt &>(expr);
}

class verilog_continuet : public verilog_statementt
{
public:
  verilog_continuet() : verilog_statementt(ID_continue)
  {
  }
};

inline const verilog_continuet &to_verilog_continue(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_continue);
  return static_cast<const verilog_continuet &>(expr);
}

inline verilog_continuet &to_verilog_continue(exprt &expr)
{
  PRECONDITION(expr.id() == ID_continue);
  return static_cast<verilog_continuet &>(expr);
}

class verilog_returnt : public verilog_statementt
{
public:
  verilog_returnt() : verilog_statementt(ID_return)
  {
  }

  explicit verilog_returnt(exprt value) : verilog_statementt(ID_return)
  {
    add_to_operands(std::move(value));
  }

  bool has_value() const
  {
    return operands().size() == 1;
  }

  exprt &value()
  {
    PRECONDITION(has_value());
    return op0();
  }

  const exprt &value() const
  {
    PRECONDITION(has_value());
    return op0();
  }
};

inline const verilog_returnt &to_verilog_return(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_return);
  return static_cast<const verilog_returnt &>(expr);
}

inline verilog_returnt &to_verilog_return(exprt &expr)
{
  PRECONDITION(expr.id() == ID_return);
  return static_cast<verilog_returnt &>(expr);
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
  verilog_procedural_continuous_assignt()
    : verilog_statementt(ID_procedural_continuous_assign)
  {
  }
};

inline const verilog_procedural_continuous_assignt &
to_verilog_procedural_continuous_assign(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_procedural_continuous_assign);
  return static_cast<const verilog_procedural_continuous_assignt &>(expr);
}

inline verilog_procedural_continuous_assignt &
to_verilog_procedural_continuous_assign(exprt &expr)
{
  PRECONDITION(expr.id() == ID_procedural_continuous_assign);
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
  verilog_blocking_assignt(const exprt &_lhs, const exprt &_rhs)
    : verilog_assignt(ID_verilog_blocking_assign, _lhs, _rhs)
  {
  }
};

inline const verilog_blocking_assignt &
to_verilog_blocking_assign(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_verilog_blocking_assign);
  return static_cast<const verilog_blocking_assignt &>(expr);
}

inline verilog_blocking_assignt &to_verilog_blocking_assign(exprt &expr)
{
  PRECONDITION(expr.id() == ID_verilog_blocking_assign);
  return static_cast<verilog_blocking_assignt &>(expr);
}

class verilog_non_blocking_assignt:public verilog_assignt
{
public:
  verilog_non_blocking_assignt()
    : verilog_assignt(ID_verilog_non_blocking_assign)
  {
  }
};

inline const verilog_non_blocking_assignt &
to_verilog_non_blocking_assign(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_verilog_non_blocking_assign);
  return static_cast<const verilog_non_blocking_assignt &>(expr);
}

inline verilog_non_blocking_assignt &to_verilog_non_blocking_assign(exprt &expr)
{
  PRECONDITION(expr.id() == ID_verilog_non_blocking_assign);
  return static_cast<verilog_non_blocking_assignt &>(expr);
}

/// Verilog static concurrent assert/assume/cover property
/// module item.
class verilog_assert_assume_cover_module_itemt : public verilog_module_itemt
{
public:
  verilog_assert_assume_cover_module_itemt(
    irep_idt __id,
    exprt __condition,
    verilog_statementt __action)
    : verilog_module_itemt(__id)
  {
    operands().resize(2);
    condition() = std::move(__condition);
    action() = std::move(__action);
  }
  
  inline exprt &condition()
  {
    return op0();
  }

  inline const exprt &condition() const
  {
    return op0();
  }

  inline exprt &action()
  {
    return op1();
  }

  inline const exprt &action() const
  {
    return op1();
  }

  // The full identifier created by the type checker
  const irep_idt &identifier() const
  {
    return get(ID_identifier);
  }

  void identifier(irep_idt identifier)
  {
    set(ID_identifier, identifier);
  }

  const irep_idt &base_name() const
  {
    return get(ID_base_name);
  }
};

inline const verilog_assert_assume_cover_module_itemt &
to_verilog_assert_assume_cover_module_item(
  const verilog_module_itemt &module_item)
{
  PRECONDITION(
    module_item.id() == ID_verilog_assert_property ||
    module_item.id() == ID_verilog_assume_property ||
    module_item.id() == ID_verilog_restrict_property ||
    module_item.id() == ID_verilog_cover_property ||
    module_item.id() == ID_verilog_cover_sequence);
  binary_exprt::check(module_item);
  return static_cast<const verilog_assert_assume_cover_module_itemt &>(
    module_item);
}

inline verilog_assert_assume_cover_module_itemt &
to_verilog_assert_assume_cover_module_item(verilog_module_itemt &module_item)
{
  PRECONDITION(
    module_item.id() == ID_verilog_assert_property ||
    module_item.id() == ID_verilog_assume_property ||
    module_item.id() == ID_verilog_restrict_property ||
    module_item.id() == ID_verilog_cover_property ||
    module_item.id() == ID_verilog_cover_sequence);
  binary_exprt::check(module_item);
  return static_cast<verilog_assert_assume_cover_module_itemt &>(module_item);
}

/// base-class for assert, assume and cover statements
class verilog_assert_assume_cover_statementt : public verilog_statementt
{
public:
  explicit verilog_assert_assume_cover_statementt(irep_idt id)
    : verilog_statementt(id)
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

  // The Verilog immediate assert/assume/cover statements
  // do not have an identifier, but the SMV-style ones do.
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

  void base_name(irep_idt _base_name)
  {
    set(ID_base_name, _base_name);
  }
};

inline const verilog_assert_assume_cover_statementt &
to_verilog_assert_assume_cover_statement(const verilog_statementt &statement)
{
  PRECONDITION(
    statement.id() == ID_verilog_immediate_assert ||
    statement.id() == ID_verilog_assert_property ||
    statement.id() == ID_verilog_smv_assert ||
    statement.id() == ID_verilog_immediate_assume ||
    statement.id() == ID_verilog_assume_property ||
    statement.id() == ID_verilog_restrict_property ||
    statement.id() == ID_verilog_smv_assume ||
    statement.id() == ID_verilog_immediate_cover ||
    statement.id() == ID_verilog_cover_property ||
    statement.id() == ID_verilog_cover_sequence);
  binary_exprt::check(statement);
  return static_cast<const verilog_assert_assume_cover_statementt &>(statement);
}

inline verilog_assert_assume_cover_statementt &
to_verilog_assert_assume_cover_statement(verilog_statementt &statement)
{
  PRECONDITION(
    statement.id() == ID_verilog_immediate_assert ||
    statement.id() == ID_verilog_assert_property ||
    statement.id() == ID_verilog_smv_assert ||
    statement.id() == ID_verilog_immediate_assume ||
    statement.id() == ID_verilog_assume_property ||
    statement.id() == ID_verilog_restrict_property ||
    statement.id() == ID_verilog_smv_assume ||
    statement.id() == ID_verilog_immediate_cover ||
    statement.id() == ID_verilog_cover_property ||
    statement.id() == ID_verilog_cover_sequence);
  binary_exprt::check(statement);
  return static_cast<verilog_assert_assume_cover_statementt &>(statement);
}

// A wrapper that encapsulates an assertion statement into an item.
class verilog_assertion_itemt : public verilog_module_itemt
{
public:
  const verilog_assert_assume_cover_statementt &statement() const
  {
    return static_cast<const verilog_assert_assume_cover_statementt &>(op0());
  }

  verilog_assert_assume_cover_statementt &statement()
  {
    return static_cast<verilog_assert_assume_cover_statementt &>(op0());
  }
};

inline const verilog_assertion_itemt &
to_verilog_assertion_item(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_verilog_assertion_item);
  validate_operands(expr, 1, "verilog_assertion_item must have 1 operand");
  return static_cast<const verilog_assertion_itemt &>(expr);
}

inline verilog_assertion_itemt &to_verilog_assertion_item(exprt &expr)
{
  PRECONDITION(expr.id() == ID_verilog_assertion_item);
  validate_operands(expr, 1, "generate_assign must have 1 operand");
  return static_cast<verilog_assertion_itemt &>(expr);
}

// Can be one of three:
// 1) Immediate assertion statement
// 2) Procedural concurrent assertion statement
// 3) SMV-style assertion statement
class verilog_assert_statementt : public verilog_assert_assume_cover_statementt
{
public:
  explicit verilog_assert_statementt(irep_idt id)
    : verilog_assert_assume_cover_statementt(id)
  {
  }
};

inline const verilog_assert_statementt &
to_verilog_assert_statement(const verilog_statementt &statement)
{
  PRECONDITION(
    statement.id() == ID_verilog_immediate_assert ||
    statement.id() == ID_verilog_assert_property ||
    statement.id() == ID_verilog_smv_assert);
  binary_exprt::check(statement);
  return static_cast<const verilog_assert_statementt &>(statement);
}

inline verilog_assert_statementt &
to_verilog_assert_statement(verilog_statementt &statement)
{
  PRECONDITION(
    statement.id() == ID_verilog_immediate_assert ||
    statement.id() == ID_verilog_assert_property ||
    statement.id() == ID_verilog_smv_assert);
  binary_exprt::check(statement);
  return static_cast<verilog_assert_statementt &>(statement);
}

// Can be one of three:
// 1) Immediate assumption statement
// 2) Procedural concurrent assumption statement
// 3) SMV-style assumption statement
class verilog_assume_statementt : public verilog_assert_assume_cover_statementt
{
public:
  verilog_assume_statementt()
    : verilog_assert_assume_cover_statementt(ID_verilog_assume_property)
  {
  }
};

inline const verilog_assume_statementt &
to_verilog_assume_statement(const verilog_statementt &statement)
{
  PRECONDITION(
    statement.id() == ID_verilog_immediate_assume ||
    statement.id() == ID_verilog_assume_property ||
    statement.id() == ID_verilog_smv_assume);
  binary_exprt::check(statement);
  return static_cast<const verilog_assume_statementt &>(statement);
}

inline verilog_assume_statementt &
to_verilog_assume_statement(verilog_statementt &statement)
{
  PRECONDITION(
    statement.id() == ID_verilog_immediate_assume ||
    statement.id() == ID_verilog_assume_property ||
    statement.id() == ID_verilog_smv_assume);
  binary_exprt::check(statement);
  return static_cast<verilog_assume_statementt &>(statement);
}

class verilog_restrict_statementt
  : public verilog_assert_assume_cover_statementt
{
public:
  verilog_restrict_statementt()
    : verilog_assert_assume_cover_statementt(ID_verilog_restrict_property)
  {
  }
};

inline const verilog_restrict_statementt &
to_verilog_restrict_statement(const verilog_statementt &statement)
{
  PRECONDITION(statement.id() == ID_verilog_restrict_property);
  binary_exprt::check(statement);
  return static_cast<const verilog_restrict_statementt &>(statement);
}

inline verilog_restrict_statementt &
to_verilog_restrict_statement(verilog_statementt &statement)
{
  PRECONDITION(statement.id() == ID_verilog_restrict_property);
  binary_exprt::check(statement);
  return static_cast<verilog_restrict_statementt &>(statement);
}

// modules, primitives, programs, interfaces, classes, packages
class verilog_item_containert : public irept
{
public:
  verilog_item_containert(irep_idt _id, irep_idt _base_name)
    : irept(_id)
  {
    base_name(_base_name);
  }

  irep_idt base_name() const
  {
    return get(ID_base_name);
  }

  void base_name(irep_idt base_name)
  {
    return set(ID_base_name, base_name);
  }

  using itemst = std::vector<class verilog_module_itemt>;

  const itemst &items() const
  {
    return (const itemst &)(find(ID_module_items).get_sub());
  }

  itemst &items()
  {
    return (itemst &)(add(ID_module_items).get_sub());
  }

  const source_locationt &source_location() const
  {
    return static_cast<const source_locationt &>(find(ID_C_source_location));
  }

  source_locationt &add_source_location()
  {
    return static_cast<source_locationt &>(add(ID_C_source_location));
  }

  // The identifiers of the modules and packages used
  // (not: the identifiers of the module instances)
  std::set<irep_idt> dependencies() const;
};

class verilog_interfacet : public verilog_item_containert
{
public:
  explicit verilog_interfacet(irep_idt _base_name)
    : verilog_item_containert(ID_verilog_module, _base_name)
  {
  }

  void show(std::ostream &) const;
};

inline const verilog_interfacet &to_verilog_interface(const irept &irep)
{
  PRECONDITION(irep.id() == ID_verilog_interface);
  return static_cast<const verilog_interfacet &>(irep);
}

inline verilog_interfacet &to_verilog_interface(irept &irep)
{
  PRECONDITION(irep.id() == ID_verilog_interface);
  return static_cast<verilog_interfacet &>(irep);
}

class verilog_module_sourcet : public verilog_item_containert
{
public:
  explicit verilog_module_sourcet(irep_idt _base_name)
    : verilog_item_containert(ID_verilog_module, _base_name)
  {
  }

  using parameter_port_declst = std::vector<verilog_parameter_declt>;

  const parameter_port_declst &parameter_port_decls() const
  {
    return (const parameter_port_declst &)(find(ID_verilog_parameter_port_decls)
                                             .get_sub());
  }

  parameter_port_declst &parameter_port_decls()
  {
    return (
      parameter_port_declst &)(add(ID_verilog_parameter_port_decls).get_sub());
  }

  using port_listt = std::vector<verilog_declt>;

  const port_listt &ports() const
  {
    return (const port_listt &)(find(ID_ports).get_sub());
  }

  using module_itemst = itemst;

  const module_itemst &module_items() const
  {
    return items();
  }

  module_itemst &module_items()
  {
    return items();
  }

  void show(std::ostream &) const;
};

inline const verilog_module_sourcet &to_verilog_module_source(const irept &irep)
{
  return static_cast<const verilog_module_sourcet &>(irep);
}

inline verilog_module_sourcet &to_verilog_module_source(irept &irep)
{
  return static_cast<verilog_module_sourcet &>(irep);
}

class verilog_checkert : public verilog_item_containert
{
public:
  explicit verilog_checkert(irep_idt _base_name)
    : verilog_item_containert(ID_verilog_module, _base_name)
  {
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

  void show(std::ostream &) const;
};

inline const verilog_checkert &to_verilog_checker(const irept &irep)
{
  PRECONDITION(irep.id() == ID_verilog_checker);
  return static_cast<const verilog_checkert &>(irep);
}

inline verilog_checkert &to_verilog_checker(irept &irep)
{
  PRECONDITION(irep.id() == ID_verilog_checker);
  return static_cast<verilog_checkert &>(irep);
}

class verilog_packaget : public verilog_item_containert
{
public:
  explicit verilog_packaget(irep_idt _base_name)
    : verilog_item_containert(ID_verilog_module, _base_name)
  {
  }

  void show(std::ostream &) const;
};

inline const verilog_packaget &to_verilog_package(const irept &irep)
{
  PRECONDITION(irep.id() == ID_verilog_package);
  return static_cast<const verilog_packaget &>(irep);
}

inline verilog_packaget &to_verilog_package(irept &irep)
{
  PRECONDITION(irep.id() == ID_verilog_package);
  return static_cast<verilog_packaget &>(irep);
}

class verilog_programt : public verilog_item_containert
{
public:
  explicit verilog_programt(irep_idt _base_name)
    : verilog_item_containert(ID_verilog_module, _base_name)
  {
  }

  void show(std::ostream &) const;
};

inline const verilog_programt &to_verilog_program(const irept &irep)
{
  PRECONDITION(irep.id() == ID_verilog_program);
  return static_cast<const verilog_programt &>(irep);
}

inline verilog_programt &to_verilog_program(irept &irep)
{
  PRECONDITION(irep.id() == ID_verilog_program);
  return static_cast<verilog_programt &>(irep);
}

class verilog_classt : public verilog_item_containert
{
public:
  explicit verilog_classt(irep_idt _base_name)
    : verilog_item_containert(ID_verilog_module, _base_name)
  {
  }

  void show(std::ostream &) const;
};

inline const verilog_classt &to_verilog_class(const irept &irep)
{
  PRECONDITION(irep.id() == ID_verilog_class);
  return static_cast<const verilog_classt &>(irep);
}

inline verilog_classt &to_verilog_class(irept &irep)
{
  PRECONDITION(irep.id() == ID_verilog_class);
  return static_cast<verilog_classt &>(irep);
}

class verilog_udpt : public verilog_item_containert
{
public:
  explicit verilog_udpt(irep_idt _base_name)
    : verilog_item_containert(ID_verilog_module, _base_name)
  {
  }

  void show(std::ostream &) const;
};

inline const verilog_udpt &to_verilog_udp(const irept &irep)
{
  PRECONDITION(irep.id() == ID_verilog_udp);
  return static_cast<const verilog_udpt &>(irep);
}

inline verilog_udpt &to_verilog_udp(irept &irep)
{
  PRECONDITION(irep.id() == ID_verilog_udp);
  return static_cast<verilog_udpt &>(irep);
}

/// size'(expression)
class verilog_explicit_size_cast_exprt : public binary_exprt
{
public:
  verilog_explicit_size_cast_exprt(exprt __size, exprt __op, typet __type)
    : binary_exprt(
        std::move(__size),
        ID_verilog_explicit_size_cast,
        std::move(__op),
        std::move(__type))
  {
  }

  const exprt &size() const
  {
    return op0();
  }

  exprt &size()
  {
    return op0();
  }

  const exprt &op() const
  {
    return op1();
  }

  exprt &op()
  {
    return op1();
  }
};

inline const verilog_explicit_size_cast_exprt &
to_verilog_explicit_size_cast_expr(const exprt &expr)
{
  verilog_explicit_size_cast_exprt::check(expr);
  return static_cast<const verilog_explicit_size_cast_exprt &>(expr);
}

inline verilog_explicit_size_cast_exprt &
to_verilog_explicit_size_cast_expr(exprt &expr)
{
  verilog_explicit_size_cast_exprt::check(expr);
  return static_cast<verilog_explicit_size_cast_exprt &>(expr);
}

class verilog_explicit_const_cast_exprt : public unary_exprt
{
public:
  verilog_explicit_const_cast_exprt(exprt __op, typet __type)
    : unary_exprt(
        ID_verilog_explicit_const_cast,
        std::move(__op),
        std::move(__type))
  {
  }

  exprt lower() const
  {
    return typecast_exprt{op(), type()};
  }
};

inline const verilog_explicit_const_cast_exprt &
to_verilog_explicit_const_cast_expr(const exprt &expr)
{
  verilog_explicit_const_cast_exprt::check(expr);
  return static_cast<const verilog_explicit_const_cast_exprt &>(expr);
}

inline verilog_explicit_const_cast_exprt &
to_verilog_explicit_const_cast_expr(exprt &expr)
{
  verilog_explicit_const_cast_exprt::check(expr);
  return static_cast<verilog_explicit_const_cast_exprt &>(expr);
}

class verilog_explicit_signing_cast_exprt : public unary_exprt
{
public:
  verilog_explicit_signing_cast_exprt(exprt __op, typet __type)
    : unary_exprt(
        ID_verilog_explicit_signing_cast,
        std::move(__op),
        std::move(__type))
  {
  }

  bool is_signed() const
  {
    auto &dest_type = type();
    return dest_type.id() == ID_signedbv ||
           dest_type.id() == ID_verilog_signedbv;
  }

  exprt lower() const
  {
    return typecast_exprt{op(), type()};
  }
};

inline const verilog_explicit_signing_cast_exprt &
to_verilog_explicit_signing_cast_expr(const exprt &expr)
{
  verilog_explicit_signing_cast_exprt::check(expr);
  return static_cast<const verilog_explicit_signing_cast_exprt &>(expr);
}

inline verilog_explicit_signing_cast_exprt &
to_verilog_explicit_signing_cast_expr(exprt &expr)
{
  verilog_explicit_signing_cast_exprt::check(expr);
  return static_cast<verilog_explicit_signing_cast_exprt &>(expr);
}

class verilog_explicit_type_cast_exprt : public unary_exprt
{
public:
  verilog_explicit_type_cast_exprt(exprt __op, typet __type)
    : unary_exprt(
        ID_verilog_explicit_type_cast,
        std::move(__op),
        std::move(__type))
  {
  }
};

inline const verilog_explicit_type_cast_exprt &
to_verilog_explicit_type_cast_expr(const exprt &expr)
{
  verilog_explicit_type_cast_exprt::check(expr);
  return static_cast<const verilog_explicit_type_cast_exprt &>(expr);
}

inline verilog_explicit_type_cast_exprt &
to_verilog_explicit_type_cast_expr(exprt &expr)
{
  verilog_explicit_type_cast_exprt::check(expr);
  return static_cast<verilog_explicit_type_cast_exprt &>(expr);
}

class verilog_implicit_typecast_exprt : public unary_exprt
{
public:
  verilog_implicit_typecast_exprt(exprt __op, typet __type)
    : unary_exprt(
        ID_verilog_implicit_typecast,
        std::move(__op),
        std::move(__type))
  {
  }
};

inline const verilog_implicit_typecast_exprt &
to_verilog_implicit_typecast_expr(const exprt &expr)
{
  verilog_implicit_typecast_exprt::check(expr);
  return static_cast<const verilog_implicit_typecast_exprt &>(expr);
}

inline verilog_implicit_typecast_exprt &
to_verilog_implicit_typecast_expr(exprt &expr)
{
  verilog_implicit_typecast_exprt::check(expr);
  return static_cast<verilog_implicit_typecast_exprt &>(expr);
}

class verilog_past_exprt : public binary_exprt
{
public:
  verilog_past_exprt(exprt __what, exprt __ticks)
    : binary_exprt(__what, ID_verilog_past, std::move(__ticks), __what.type())
  {
  }

  const exprt &what() const
  {
    return op0();
  }

  exprt &what()
  {
    return op0();
  }

  const exprt &ticks() const
  {
    return op1();
  }

  exprt &ticks()
  {
    return op1();
  }

  /// value when going beyond the initial time frame
  exprt default_value() const;
};

inline const verilog_past_exprt &to_verilog_past_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_verilog_past);
  verilog_past_exprt::check(expr);
  return static_cast<const verilog_past_exprt &>(expr);
}

inline verilog_past_exprt &to_verilog_past_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_verilog_past);
  verilog_past_exprt::check(expr);
  return static_cast<verilog_past_exprt &>(expr);
}

class verilog_non_indexed_part_select_exprt : public ternary_exprt
{
public:
  verilog_non_indexed_part_select_exprt(
    exprt src,
    exprt msb,
    exprt lsb,
    typet type)
    : ternary_exprt(
        ID_verilog_non_indexed_part_select,
        std::move(src),
        std::move(msb),
        std::move(lsb),
        std::move(type))
  {
  }

  const exprt &src() const
  {
    return op0();
  }

  exprt &src()
  {
    return op0();
  }

  const exprt &msb() const
  {
    return op1();
  }

  exprt &msb()
  {
    return op1();
  }

  const exprt &lsb() const
  {
    return op2();
  }

  exprt &lsb()
  {
    return op2();
  }

  // lowering to extractbits
  exprt lower() const;
};

inline const verilog_non_indexed_part_select_exprt &
to_verilog_non_indexed_part_select_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_verilog_non_indexed_part_select);
  verilog_non_indexed_part_select_exprt::check(expr);
  return static_cast<const verilog_non_indexed_part_select_exprt &>(expr);
}

inline verilog_non_indexed_part_select_exprt &
to_verilog_non_indexed_part_select_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_verilog_non_indexed_part_select);
  verilog_non_indexed_part_select_exprt::check(expr);
  return static_cast<verilog_non_indexed_part_select_exprt &>(expr);
}

class verilog_indexed_part_select_plus_or_minus_exprt : public ternary_exprt
{
public:
  verilog_indexed_part_select_plus_or_minus_exprt(
    irep_idt id,
    exprt src,
    exprt index,
    exprt width,
    typet type)
    : ternary_exprt(
        id,
        std::move(src),
        std::move(index),
        std::move(width),
        std::move(type))
  {
  }

  const exprt &src() const
  {
    return op0();
  }

  exprt &src()
  {
    return op0();
  }

  const exprt &index() const
  {
    return op1();
  }

  exprt &index()
  {
    return op1();
  }

  const exprt &width() const
  {
    return op2();
  }

  exprt &width()
  {
    return op2();
  }

  exprt lower() const;
};

inline const verilog_indexed_part_select_plus_or_minus_exprt &
to_verilog_indexed_part_select_plus_or_minus_expr(const exprt &expr)
{
  PRECONDITION(
    expr.id() == ID_verilog_indexed_part_select_plus ||
    expr.id() == ID_verilog_indexed_part_select_minus);
  verilog_indexed_part_select_plus_or_minus_exprt::check(expr);
  return static_cast<const verilog_indexed_part_select_plus_or_minus_exprt &>(
    expr);
}

inline verilog_indexed_part_select_plus_or_minus_exprt &
to_verilog_indexed_part_select_plus_or_minus_expr(exprt &expr)
{
  PRECONDITION(
    expr.id() == ID_verilog_indexed_part_select_plus ||
    expr.id() == ID_verilog_indexed_part_select_minus);
  verilog_indexed_part_select_plus_or_minus_exprt::check(expr);
  return static_cast<verilog_indexed_part_select_plus_or_minus_exprt &>(expr);
}

/// a base class for both sequence and property declarations
class verilog_sequence_property_declaration_baset : public verilog_module_itemt
{
public:
  verilog_sequence_property_declaration_baset(irep_idt _id, exprt _cond)
    : verilog_module_itemt{_id}
  {
    add_to_operands(std::move(_cond));
  }

  const irep_idt &base_name() const
  {
    return get(ID_base_name);
  }

  const exprt &cond() const
  {
    return op0();
  }

  exprt &cond()
  {
    return op0();
  }
};

inline const verilog_sequence_property_declaration_baset &
to_verilog_sequence_property_declaration_base(const exprt &expr)
{
  PRECONDITION(
    expr.id() == ID_verilog_sequence_declaration ||
    expr.id() == ID_verilog_property_declaration);
  verilog_sequence_property_declaration_baset::check(expr);
  return static_cast<const verilog_sequence_property_declaration_baset &>(expr);
}

inline verilog_sequence_property_declaration_baset &
to_verilog_sequence_property_declaration_base(exprt &expr)
{
  PRECONDITION(
    expr.id() == ID_verilog_sequence_declaration ||
    expr.id() == ID_verilog_property_declaration);
  verilog_sequence_property_declaration_baset::check(expr);
  return static_cast<verilog_sequence_property_declaration_baset &>(expr);
}

class verilog_property_declarationt
  : public verilog_sequence_property_declaration_baset
{
public:
  explicit verilog_property_declarationt(exprt property)
    : verilog_sequence_property_declaration_baset{
        ID_verilog_property_declaration,
        std::move(property)}
  {
  }

  const exprt &property() const
  {
    return cond();
  }

  exprt &property()
  {
    return cond();
  }
};

inline const verilog_property_declarationt &
to_verilog_property_declaration(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_verilog_property_declaration);
  verilog_property_declarationt::check(expr);
  return static_cast<const verilog_property_declarationt &>(expr);
}

inline verilog_property_declarationt &
to_verilog_property_declaration(exprt &expr)
{
  PRECONDITION(expr.id() == ID_verilog_property_declaration);
  verilog_property_declarationt::check(expr);
  return static_cast<verilog_property_declarationt &>(expr);
}

class verilog_sequence_declarationt
  : public verilog_sequence_property_declaration_baset
{
public:
  explicit verilog_sequence_declarationt(exprt _sequence)
    : verilog_sequence_property_declaration_baset{
        ID_verilog_sequence_declaration,
        std::move(_sequence)}
  {
  }

  const exprt &sequence() const
  {
    return cond();
  }

  exprt &sequence()
  {
    return cond();
  }
};

inline const verilog_sequence_declarationt &
to_verilog_sequence_declaration(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_verilog_sequence_declaration);
  verilog_sequence_declarationt::check(expr);
  return static_cast<const verilog_sequence_declarationt &>(expr);
}

inline verilog_sequence_declarationt &
to_verilog_sequence_declaration(exprt &expr)
{
  PRECONDITION(expr.id() == ID_verilog_sequence_declaration);
  verilog_sequence_declarationt::check(expr);
  return static_cast<verilog_sequence_declarationt &>(expr);
}

class verilog_streaming_concatenation_exprt : public exprt
{
public:
  bool has_slice_size() const
  {
    return operands().size() == 2;
  }

  // optional
  const exprt &slice_size() const
  {
    PRECONDITION(has_slice_size());
    return op0();
  }

  const exprt::operandst &stream_expressions() const
  {
    return has_slice_size() ? op1().operands() : op0().operands();
  }

  // lower to bitreverse or similar
  exprt lower() const;
};

inline const verilog_streaming_concatenation_exprt &
to_verilog_streaming_concatenation_expr(const exprt &expr)
{
  return static_cast<const verilog_streaming_concatenation_exprt &>(expr);
}

inline verilog_streaming_concatenation_exprt &
to_verilog_streaming_concatenation_expr(exprt &expr)
{
  return static_cast<verilog_streaming_concatenation_exprt &>(expr);
}

class verilog_inside_exprt : public binary_exprt
{
public:
  verilog_inside_exprt(exprt _op, exprt::operandst _range_list)
    : binary_exprt(
        std::move(_op),
        ID_verilog_inside,
        exprt{irep_idt{}, typet{}, std::move(_range_list)})
  {
  }

  const exprt &op() const
  {
    return op0();
  }

  const exprt::operandst &range_list() const
  {
    return op1().operands();
  }

  // lower to ==, ==?, >=, <=
  exprt lower() const;
};

inline const verilog_inside_exprt &to_verilog_inside_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_verilog_inside);
  verilog_inside_exprt::check(expr);
  return static_cast<const verilog_inside_exprt &>(expr);
}

inline verilog_inside_exprt &to_verilog_inside_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_verilog_inside);
  verilog_inside_exprt::check(expr);
  return static_cast<verilog_inside_exprt &>(expr);
}

class verilog_value_range_exprt : public binary_exprt
{
public:
  verilog_value_range_exprt(exprt from, exprt to)
    : binary_exprt(std::move(from), ID_verilog_value_range, std::move(to))
  {
  }

  // lower to >=, <=
  exprt lower() const;
};

inline const verilog_value_range_exprt &
to_verilog_value_range_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_verilog_value_range);
  verilog_value_range_exprt::check(expr);
  return static_cast<const verilog_value_range_exprt &>(expr);
}

inline verilog_value_range_exprt &to_verilog_value_range_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_verilog_value_range);
  verilog_value_range_exprt::check(expr);
  return static_cast<verilog_value_range_exprt &>(expr);
}

/// package::identifier
class verilog_package_scope_exprt : public binary_exprt
{
public:
  irep_idt package_base_name() const
  {
    return op0().id();
  }

  const exprt &identifier() const
  {
    return op1();
  }
};

/// Cast a generic typet to a \ref verilog_package_scope_exprt. This is an unchecked
/// conversion. \a type must be known to be \ref verilog_package_scope_exprt.
/// \param type: Source type
/// \return Object of type \ref verilog_package_scope_exprt
inline const verilog_package_scope_exprt &
to_verilog_package_scope_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_verilog_package_scope);
  verilog_package_scope_exprt::check(expr);
  return static_cast<const verilog_package_scope_exprt &>(expr);
}

/// \copydoc to_verilog_exprdef_expr(const exprt &)
inline verilog_package_scope_exprt &to_verilog_package_scope_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_verilog_package_scope);
  verilog_package_scope_exprt::check(expr);
  return static_cast<verilog_package_scope_exprt &>(expr);
}

class reduction_and_exprt : public unary_predicate_exprt
{
public:
  explicit reduction_and_exprt(exprt _op)
    : unary_predicate_exprt(ID_reduction_and, std::move(_op))
  {
  }
};

template <>
inline bool can_cast_expr<reduction_and_exprt>(const exprt &expr)
{
  reduction_and_exprt::check(expr);
  return expr.id() == ID_reduction_and;
}

inline const reduction_and_exprt &to_reduction_and_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_reduction_and);
  reduction_and_exprt::check(expr);
  return static_cast<const reduction_and_exprt &>(expr);
}

inline reduction_and_exprt &to_reduction_and_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_reduction_and);
  reduction_and_exprt::check(expr);
  return static_cast<reduction_and_exprt &>(expr);
}

class reduction_or_exprt : public unary_predicate_exprt
{
public:
  explicit reduction_or_exprt(exprt _op)
    : unary_predicate_exprt(ID_reduction_or, std::move(_op))
  {
  }
};

template <>
inline bool can_cast_expr<reduction_or_exprt>(const exprt &expr)
{
  reduction_or_exprt::check(expr);
  return expr.id() == ID_reduction_or;
}

inline const reduction_or_exprt &to_reduction_or_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_reduction_or);
  reduction_or_exprt::check(expr);
  return static_cast<const reduction_or_exprt &>(expr);
}

inline reduction_or_exprt &to_reduction_or_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_reduction_or);
  reduction_or_exprt::check(expr);
  return static_cast<reduction_or_exprt &>(expr);
}

class reduction_nor_exprt : public unary_predicate_exprt
{
public:
  explicit reduction_nor_exprt(exprt _op)
    : unary_predicate_exprt(ID_reduction_nor, std::move(_op))
  {
  }
};

template <>
inline bool can_cast_expr<reduction_nor_exprt>(const exprt &expr)
{
  reduction_nor_exprt::check(expr);
  return expr.id() == ID_reduction_nor;
}

inline const reduction_nor_exprt &to_reduction_nor_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_reduction_nor);
  reduction_nor_exprt::check(expr);
  return static_cast<const reduction_nor_exprt &>(expr);
}

inline reduction_nor_exprt &to_reduction_nor_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_reduction_nor);
  reduction_nor_exprt::check(expr);
  return static_cast<reduction_nor_exprt &>(expr);
}

class reduction_nand_exprt : public unary_predicate_exprt
{
public:
  explicit reduction_nand_exprt(exprt _op)
    : unary_predicate_exprt(ID_reduction_nand, std::move(_op))
  {
  }
};

template <>
inline bool can_cast_expr<reduction_nand_exprt>(const exprt &expr)
{
  reduction_nand_exprt::check(expr);
  return expr.id() == ID_reduction_nand;
}

inline const reduction_nand_exprt &to_reduction_nand_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_reduction_nand);
  reduction_nand_exprt::check(expr);
  return static_cast<const reduction_nand_exprt &>(expr);
}

inline reduction_nand_exprt &to_reduction_nand_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_reduction_nand);
  reduction_nand_exprt::check(expr);
  return static_cast<reduction_nand_exprt &>(expr);
}

class reduction_xor_exprt : public unary_predicate_exprt
{
public:
  explicit reduction_xor_exprt(exprt _op)
    : unary_predicate_exprt(ID_reduction_xor, std::move(_op))
  {
  }
};

template <>
inline bool can_cast_expr<reduction_xor_exprt>(const exprt &expr)
{
  reduction_xor_exprt::check(expr);
  return expr.id() == ID_reduction_xor;
}

inline const reduction_xor_exprt &to_reduction_xor_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_reduction_xor);
  reduction_xor_exprt::check(expr);
  return static_cast<const reduction_xor_exprt &>(expr);
}

inline reduction_xor_exprt &to_reduction_xor_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_reduction_xor);
  reduction_xor_exprt::check(expr);
  return static_cast<reduction_xor_exprt &>(expr);
}

class reduction_xnor_exprt : public unary_predicate_exprt
{
public:
  explicit reduction_xnor_exprt(exprt _op)
    : unary_predicate_exprt(ID_reduction_xnor, std::move(_op))
  {
  }
};

template <>
inline bool can_cast_expr<reduction_xnor_exprt>(const exprt &expr)
{
  reduction_xnor_exprt::check(expr);
  return expr.id() == ID_reduction_xnor;
}

inline const reduction_xnor_exprt &to_reduction_xnor_expr(const exprt &expr)
{
  PRECONDITION(expr.id() == ID_reduction_xnor);
  reduction_xnor_exprt::check(expr);
  return static_cast<const reduction_xnor_exprt &>(expr);
}

inline reduction_xnor_exprt &to_reduction_xnor_expr(exprt &expr)
{
  PRECONDITION(expr.id() == ID_reduction_xnor);
  reduction_xnor_exprt::check(expr);
  return static_cast<reduction_xnor_exprt &>(expr);
}

#endif
