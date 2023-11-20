/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_VERILOG_EXPR_H
#define CPROVER_VERILOG_EXPR_H

#include <cassert>

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
  inline explicit verilog_module_exprt() : exprt(ID_verilog_module)
  {
  }

  using module_itemst = std::vector<class verilog_module_itemt>;

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
    irep_idt _identifier,
    verilog_module_exprt::module_itemst _module_items)
    : verilog_module_itemt(ID_generate_block)
  {
    set(ID_identifier, _identifier);
    module_items() = std::move(_module_items);
  }

  const irep_idt &identifier() const
  {
    return get(ID_identifier);
  }

  bool is_named() const
  {
    return !identifier().empty();
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

class verilog_parameter_declt : public verilog_module_itemt
{
public:
  inline verilog_parameter_declt() : verilog_module_itemt(ID_parameter_decl)
  {
  }

  class declaratort : public irept
  {
  public:
    const irep_idt &identifier() const
    {
      return get(ID_identifier);
    }

    const exprt &value() const
    {
      return static_cast<const exprt &>(find(ID_value));
    }

    exprt &value()
    {
      return static_cast<exprt &>(add(ID_value));
    }
  };

  using declaratorst = std::vector<declaratort>;

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

class verilog_instt:public verilog_module_itemt
{
public:
  inline verilog_instt():verilog_module_itemt(ID_inst)
  {
  }

  inline irep_idt get_module() const { return get(ID_module); }
  
  inline void set_module(const irep_idt &module) { return set(ID_module, module); }
  
  inline exprt::operandst &parameter_assignments()
  {
    return static_cast<exprt &>(add(ID_parameter_assignments)).operands();
  }

  inline const exprt::operandst &parameter_assignments() const
  {
    return static_cast<const exprt &>(find(ID_parameter_assignments)).operands();
  }
};

inline const verilog_instt &to_verilog_inst(const exprt &expr)
{
  assert(expr.id()==ID_inst);
  return static_cast<const verilog_instt &>(expr);
}

inline verilog_instt &to_verilog_inst(exprt &expr)
{
  assert(expr.id()==ID_inst);
  return static_cast<verilog_instt &>(expr);
}

class verilog_inst_builtint:public verilog_module_itemt
{
public:
  inline verilog_inst_builtint():verilog_module_itemt(ID_inst_builtin)
  {
  }
  
  inline irep_idt get_module() const { return get(ID_module); }
};

inline const verilog_inst_builtint &to_verilog_inst_builtin(const exprt &expr)
{
  assert(expr.id()==ID_inst_builtin);
  return static_cast<const verilog_inst_builtint &>(expr);
}

inline verilog_inst_builtint &to_verilog_inst_builtin(exprt &expr)
{
  assert(expr.id()==ID_inst_builtin);
  return static_cast<verilog_inst_builtint &>(expr);
}

class verilog_alwayst:public verilog_statementt
{
public:
  verilog_alwayst():verilog_statementt(ID_always)
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

inline const verilog_alwayst &to_verilog_always(const exprt &expr)
{
  assert(expr.id()==ID_always && expr.operands().size()==1);
  return static_cast<const verilog_alwayst &>(expr);
}

inline verilog_alwayst &to_verilog_always(exprt &expr)
{
  assert(expr.id()==ID_always && expr.operands().size()==1);
  return static_cast<verilog_alwayst &>(expr);
}

class verilog_declt:public verilog_statementt
{
public:
  verilog_declt():verilog_statementt(ID_decl)
  {
  }
  
  inline irep_idt get_identifier() const
  {
    return find(ID_symbol).get(ID_identifier);
  }
  
  inline void set_identifier(const irep_idt &identifier)
  {
    add(ID_symbol).set(ID_identifier, identifier);
  }
  
  inline irep_idt get_class() const
  {
    return get(ID_class);
  }
  
  inline void set_class(const irep_idt &_class)
  {
    set(ID_class, _class);
  }

  // Function and task declarations may contain further declarations.
  using declarationst = std::vector<verilog_declt>;

  inline declarationst &declarations()
  {
    return (declarationst &)(add("declarations").get_sub());
  }

  inline const declarationst &declarations() const
  {
    return (const declarationst &)(find("declarations").get_sub());
  }

  // Function and task declarations have a body.
  inline verilog_statementt &body()
  {
    return static_cast<verilog_statementt &>(add(ID_body));
  }

  inline const verilog_statementt &body() const
  {
    return static_cast<const verilog_statementt &>(find(ID_body));
  }
};

inline const verilog_declt &to_verilog_decl(const irept &irep)
{
  assert(irep.id()==ID_decl);
  return static_cast<const verilog_declt &>(irep);
}

inline verilog_declt &to_verilog_decl(exprt &irep)
{
  assert(irep.id()==ID_decl);
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
  assert(expr.id()==ID_initial && expr.operands().size()==1);
  return static_cast<const verilog_initialt &>(expr);
}

inline verilog_initialt &to_verilog_initial(exprt &expr)
{
  assert(expr.id()==ID_initial && expr.operands().size()==1);
  return static_cast<verilog_initialt &>(expr);
}

class verilog_blockt:public verilog_statementt
{
public:
  verilog_blockt():verilog_statementt(ID_block)
  {
  }
  
  inline irep_idt get_identifier() const
  {
    return get(ID_identifier);
  }
  
  inline bool is_named() const
  {
    return !get(ID_identifier).empty();
  }
};

inline const verilog_blockt &to_verilog_block(const exprt &expr)
{
  assert(expr.id()==ID_block);
  return static_cast<const verilog_blockt &>(expr);
}

inline verilog_blockt &to_verilog_block(exprt &expr)
{
  assert(expr.id()==ID_block);
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
  assert(expr.id()=="case_item" && expr.operands().size()==2);
  return static_cast<const verilog_case_itemt &>(expr);
}

inline verilog_case_itemt &to_verilog_case_item(exprt &expr)
{
  assert(expr.id()=="case_item" && expr.operands().size()==2);
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
  assert(expr.id()==ID_case && expr.operands().size()>=1);
  return static_cast<const verilog_caset &>(expr);
}

inline verilog_caset &to_verilog_case(exprt &expr)
{
  assert(expr.id()==ID_case && expr.operands().size()>=1);
  return static_cast<verilog_caset &>(expr);
}

class verilog_ift:public verilog_statementt
{
public:
  verilog_ift():verilog_statementt(ID_if)
  {
    operands().resize(3);
  }

  exprt &condition()
  {
    return op0();
  }

  const exprt &condition() const
  {
    return op0();
  }
  
  verilog_statementt &true_case()
  {
    return static_cast<verilog_statementt &>(op1());
  }

  const verilog_statementt &true_case() const
  {
    return static_cast<const verilog_statementt &>(op1());
  }

  verilog_statementt &false_case()
  {
    return static_cast<verilog_statementt &>(op2());
  }

  const verilog_statementt &false_case() const
  {
    return static_cast<const verilog_statementt &>(op2());
  }
};

inline const verilog_ift &to_verilog_if(const exprt &expr)
{
  assert(expr.id()==ID_if && expr.operands().size()>=2);
  return static_cast<const verilog_ift &>(expr);
}

inline verilog_ift &to_verilog_if(exprt &expr)
{
  assert(expr.id()==ID_if && expr.operands().size()>=2);
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
  assert(expr.id()==ID_function_call && expr.operands().size()==2);
  return static_cast<const verilog_function_callt &>(expr);
}

inline verilog_function_callt &to_verilog_function_call(exprt &expr)
{
  assert(expr.id()==ID_function_call && expr.operands().size()==2);
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
  assert(expr.id()==ID_event_guard && expr.operands().size()==2);
  return static_cast<const verilog_event_guardt &>(expr);
}

inline verilog_event_guardt &to_verilog_event_guard(exprt &expr)
{
  assert(expr.id()==ID_event_guard && expr.operands().size()==2);
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
  assert(expr.id()==ID_delay && expr.operands().size()==2);
  return static_cast<const verilog_delayt &>(expr);
}

inline verilog_delayt &to_verilog_delay(exprt &expr)
{
  assert(expr.id()==ID_delay && expr.operands().size()==2);
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
  assert(expr.id()==ID_for && expr.operands().size()==4);
  return static_cast<const verilog_fort &>(expr);
}

inline verilog_fort &to_verilog_for(exprt &expr)
{
  assert(expr.id()==ID_for && expr.operands().size()==4);
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
  assert(expr.id()==ID_forever && expr.operands().size()==1);
  return static_cast<const verilog_forevert &>(expr);
}

inline verilog_forevert &to_verilog_forever(exprt &expr)
{
  assert(expr.id()==ID_forever && expr.operands().size()==1);
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
  assert(expr.id()==ID_while && expr.operands().size()==2);
  return static_cast<const verilog_whilet &>(expr);
}

inline verilog_whilet &to_verilog_while(exprt &expr)
{
  assert(expr.id()==ID_while && expr.operands().size()==2);
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
  assert(expr.id()==ID_repeat && expr.operands().size()==2);
  return static_cast<const verilog_repeatt &>(expr);
}

inline verilog_repeatt &to_verilog_repeat(exprt &expr)
{
  assert(expr.id()==ID_repeat && expr.operands().size()==2);
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
  assert(expr.id()==ID_continuous_assign);
  return static_cast<const verilog_procedural_continuous_assignt &>(expr);
}

inline verilog_procedural_continuous_assignt &
to_verilog_procedural_continuous_assign(exprt &expr)
{
  assert(expr.id()==ID_continuous_assign);
  return static_cast<verilog_procedural_continuous_assignt &>(expr);
}

class verilog_forcet:public verilog_statementt
{
public:
  verilog_forcet():verilog_statementt(ID_force)
  {
    operands().resize(2);
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
  assert(expr.id()==ID_force && expr.operands().size()==2);
  return static_cast<const verilog_forcet &>(expr);
}

inline verilog_forcet &to_verilog_force(exprt &expr)
{
  assert(expr.id()==ID_force && expr.operands().size()==2);
  return static_cast<verilog_forcet &>(expr);
}

class verilog_continuous_assignt:public verilog_module_itemt
{
public:
  explicit verilog_continuous_assignt(exprt assignment)
    : verilog_module_itemt(ID_continuous_assign)
  {
    add_to_operands(std::move(assignment));
  }
};

inline const verilog_continuous_assignt &
to_verilog_continuous_assign(const exprt &expr)
{
  assert(expr.id()==ID_continuous_assign);
  return static_cast<const verilog_continuous_assignt &>(expr);
}

inline verilog_continuous_assignt &to_verilog_continuous_assign(exprt &expr)
{
  assert(expr.id()==ID_continuous_assign);
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
  assert(expr.id() == ID_parameter_override);
  return static_cast<const verilog_parameter_overridet &>(expr);
}

inline verilog_parameter_overridet &to_verilog_parameter_override(exprt &expr)
{
  assert(expr.id() == ID_parameter_override);
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
  assert(expr.id()==ID_blocking_assign);
  return static_cast<const verilog_blocking_assignt &>(expr);
}

inline verilog_blocking_assignt &to_verilog_blocking_assign(exprt &expr)
{
  assert(expr.id()==ID_blocking_assign);
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
  assert(expr.id()==ID_non_blocking_assign);
  return static_cast<const verilog_non_blocking_assignt &>(expr);
}

inline verilog_non_blocking_assignt &to_verilog_non_blocking_assign(exprt &expr)
{
  assert(expr.id()==ID_non_blocking_assign);
  return static_cast<verilog_non_blocking_assignt &>(expr);
}

class verilog_assertt:public verilog_statementt
{
public:
  verilog_assertt():verilog_statementt(ID_assert)
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
};

inline const verilog_assertt &to_verilog_assert(const exprt &expr)
{
  assert(expr.id()==ID_assert && expr.operands().size()==2);
  return static_cast<const verilog_assertt &>(expr);
}

inline verilog_assertt &to_verilog_assert(exprt &expr)
{
  assert(expr.id()==ID_assert && expr.operands().size()==2);
  return static_cast<verilog_assertt &>(expr);
}

class verilog_assumet:public verilog_statementt
{
public:
  verilog_assumet():verilog_statementt(ID_assume)
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
};

inline const verilog_assumet &to_verilog_assume(const exprt &expr)
{
  assert(expr.id()==ID_assume && expr.operands().size()==2);
  return static_cast<const verilog_assumet &>(expr);
}

inline verilog_assumet &to_verilog_assume(exprt &expr)
{
  assert(expr.id()==ID_assume && expr.operands().size()==2);
  return static_cast<verilog_assumet &>(expr);
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

  const exprt::operandst &ports() const
  {
    return (const exprt::operandst &)(find(ID_ports).get_sub());
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
