/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_VERILOG_EXPR_H
#define CPROVER_VERILOG_EXPR_H

#include <cassert>

#include <util/expr.h>

class hierarchical_identifier_exprt:public exprt
{
public:
  hierarchical_identifier_exprt():exprt(ID_hierarchical_identifier)
  {
    operands().resize(2);
  }
};

extern inline const hierarchical_identifier_exprt
  &to_hierarchical_identifier_expr(const exprt &expr)
{
  assert(expr.id()==ID_hierarchical_identifier && expr.operands().size()==2);
  return static_cast<const hierarchical_identifier_exprt &>(expr);
}

extern inline hierarchical_identifier_exprt
  &to_hierarchical_identifier_expr(exprt &expr)
{
  assert(expr.id()==ID_hierarchical_identifier && expr.operands().size()==2);
  return static_cast<hierarchical_identifier_exprt &>(expr);
}

class function_call_exprt:public exprt
{
public:
  function_call_exprt()
  {
    id(ID_function_call);
    operands().resize(2);
  }

  exprt &function() { return op0(); }
  const exprt &function() const { return op0(); }

  exprt::operandst &arguments()
  {
    return op1().operands();
  }

  const exprt::operandst &arguments() const
  {
    return op1().operands();
  }
};

extern inline const function_call_exprt &to_function_call_expr(const exprt &expr)
{
  assert(expr.id()==ID_function_call && expr.operands().size()>=1);
  return static_cast<const function_call_exprt &>(expr);
}

extern inline function_call_exprt &to_function_call_expr(exprt &expr)
{
  assert(expr.id()==ID_function_call && expr.operands().size()>=1);
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

extern inline const verilog_statementt &to_verilog_statement(const exprt &expr)
{
  return static_cast<const verilog_statementt &>(expr);
}

extern inline verilog_statementt &to_verilog_statement(exprt &expr)
{
  return static_cast<verilog_statementt &>(expr);
}

class verilog_module_itemt:public exprt
{
public:
  explicit verilog_module_itemt(const irep_idt &id):exprt(id)
  {
  }
  
  verilog_module_itemt()
  {
  }
};

extern inline const verilog_module_itemt &to_verilog_module_item(const irept &irep)
{
  return static_cast<const verilog_module_itemt &>(irep);
}

extern inline verilog_module_itemt &to_verilog_module_item(irept &irep)
{
  return static_cast<verilog_module_itemt &>(irep);
}

class verilog_instt:public verilog_module_itemt
{
public:
  verilog_instt():verilog_module_itemt(ID_inst)
  {
  }
};

extern inline const verilog_instt &to_verilog_inst(const exprt &expr)
{
  assert(expr.id()==ID_inst);
  return static_cast<const verilog_instt &>(expr);
}

extern inline verilog_instt &to_verilog_inst(exprt &expr)
{
  assert(expr.id()==ID_inst);
  return static_cast<verilog_instt &>(expr);
}

class verilog_inst_builtint:public verilog_module_itemt
{
public:
  verilog_inst_builtint():verilog_module_itemt(ID_inst_builtin)
  {
  }
};

extern inline const verilog_inst_builtint &to_verilog_inst_builtin(const exprt &expr)
{
  assert(expr.id()==ID_inst_builtin);
  return static_cast<const verilog_inst_builtint &>(expr);
}

extern inline verilog_inst_builtint &to_verilog_inst_builtin(exprt &expr)
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

extern inline const verilog_alwayst &to_verilog_always(const exprt &expr)
{
  assert(expr.id()==ID_always && expr.operands().size()==1);
  return static_cast<const verilog_alwayst &>(expr);
}

extern inline verilog_alwayst &to_verilog_always(exprt &expr)
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
  
  inline irept::subt &declarations()
  {
    return add("declarations").get_sub();
  }

  inline const irept::subt &declarations() const
  {
    return find("declarations").get_sub();
  }

  inline verilog_statementt &body()
  {
    return static_cast<verilog_statementt &>(add(ID_body));
  }

  inline const verilog_statementt &body() const
  {
    return static_cast<const verilog_statementt &>(find(ID_body));
  }
};

extern inline const verilog_declt &to_verilog_decl(const irept &irep)
{
  assert(irep.id()==ID_decl);
  return static_cast<const verilog_declt &>(irep);
}

extern inline verilog_declt &to_verilog_decl(exprt &irep)
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

extern inline const verilog_initialt &to_verilog_initial(const exprt &expr)
{
  assert(expr.id()==ID_initial && expr.operands().size()==1);
  return static_cast<const verilog_initialt &>(expr);
}

extern inline verilog_initialt &to_verilog_initial(exprt &expr)
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
};

extern inline const verilog_blockt &to_verilog_block(const exprt &expr)
{
  assert(expr.id()==ID_block);
  return static_cast<const verilog_blockt &>(expr);
}

extern inline verilog_blockt &to_verilog_block(exprt &expr)
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

extern inline const verilog_case_itemt &to_verilog_case_item(const exprt &expr)
{
  assert(expr.id()=="case_item" && expr.operands().size()==2);
  return static_cast<const verilog_case_itemt &>(expr);
}

extern inline verilog_case_itemt &to_verilog_case_item(exprt &expr)
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

extern inline const verilog_caset &to_verilog_case(const exprt &expr)
{
  assert(expr.id()==ID_case && expr.operands().size()>=1);
  return static_cast<const verilog_caset &>(expr);
}

extern inline verilog_caset &to_verilog_case(exprt &expr)
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

extern inline const verilog_ift &to_verilog_if(const exprt &expr)
{
  assert(expr.id()==ID_if && expr.operands().size()>=2);
  return static_cast<const verilog_ift &>(expr);
}

extern inline verilog_ift &to_verilog_if(exprt &expr)
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

extern inline const verilog_function_callt &to_verilog_function_call(const exprt &expr)
{
  assert(expr.id()==ID_function_call && expr.operands().size()==2);
  return static_cast<const verilog_function_callt &>(expr);
}

extern inline verilog_function_callt &to_verilog_function_call(exprt &expr)
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

extern inline const verilog_event_guardt &to_verilog_event_guard(const exprt &expr)
{
  assert(expr.id()==ID_event_guard && expr.operands().size()==2);
  return static_cast<const verilog_event_guardt &>(expr);
}

extern inline verilog_event_guardt &to_verilog_event_guard(exprt &expr)
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

extern inline const verilog_delayt &to_verilog_delay(const exprt &expr)
{
  assert(expr.id()==ID_delay && expr.operands().size()==2);
  return static_cast<const verilog_delayt &>(expr);
}

extern inline verilog_delayt &to_verilog_delay(exprt &expr)
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

extern inline const verilog_fort &to_verilog_for(const exprt &expr)
{
  assert(expr.id()==ID_for && expr.operands().size()==4);
  return static_cast<const verilog_fort &>(expr);
}

extern inline verilog_fort &to_verilog_for(exprt &expr)
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

extern inline const verilog_forevert &to_verilog_forever(const exprt &expr)
{
  assert(expr.id()==ID_forever && expr.operands().size()==1);
  return static_cast<const verilog_forevert &>(expr);
}

extern inline verilog_forevert &to_verilog_forever(exprt &expr)
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

extern inline const verilog_whilet &to_verilog_while(const exprt &expr)
{
  assert(expr.id()==ID_while && expr.operands().size()==2);
  return static_cast<const verilog_whilet &>(expr);
}

extern inline verilog_whilet &to_verilog_while(exprt &expr)
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

extern inline const verilog_repeatt &to_verilog_repeat(const exprt &expr)
{
  assert(expr.id()==ID_repeat && expr.operands().size()==2);
  return static_cast<const verilog_repeatt &>(expr);
}

extern inline verilog_repeatt &to_verilog_repeat(exprt &expr)
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

extern inline const verilog_procedural_continuous_assignt &to_verilog_procedural_continuous_assign(const exprt &expr)
{
  assert(expr.id()==ID_continuous_assign);
  return static_cast<const verilog_procedural_continuous_assignt &>(expr);
}

extern inline verilog_procedural_continuous_assignt &to_verilog_procedural_continuous_assign(exprt &expr)
{
  assert(expr.id()==ID_continuous_assign);
  return static_cast<verilog_procedural_continuous_assignt &>(expr);
}

class verilog_continuous_assignt:public verilog_module_itemt
{
public:
  verilog_continuous_assignt():verilog_module_itemt(ID_continuous_assign)
  {
  }
};

extern inline const verilog_continuous_assignt &to_verilog_continuous_assign(const exprt &expr)
{
  assert(expr.id()==ID_continuous_assign);
  return static_cast<const verilog_continuous_assignt &>(expr);
}

extern inline verilog_continuous_assignt &to_verilog_continuous_assign(exprt &expr)
{
  assert(expr.id()==ID_continuous_assign);
  return static_cast<verilog_continuous_assignt &>(expr);
}

class verilog_assignt:public verilog_statementt
{
public:
  // both blocking and non-blocking
  verilog_assignt()
  {
    operands().resize(2);
  }

  verilog_assignt(const irep_idt &_id):verilog_statementt(_id)
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

extern inline const verilog_assignt &to_verilog_assign(const exprt &expr)
{
  return static_cast<const verilog_assignt &>(expr);
}

extern inline verilog_assignt &to_verilog_assign(exprt &expr)
{
  return static_cast<verilog_assignt &>(expr);
}

class verilog_blocking_assignt:public verilog_assignt
{
public:
  verilog_blocking_assignt():verilog_assignt(ID_blocking_assign)
  {
  }
};

class verilog_non_blocking_assignt:public verilog_assignt
{
public:
  verilog_non_blocking_assignt():verilog_assignt(ID_non_blocking_assign)
  {
  }
};

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

extern inline const verilog_assertt &to_verilog_assert(const exprt &expr)
{
  assert(expr.id()==ID_assert && expr.operands().size()==2);
  return static_cast<const verilog_assertt &>(expr);
}

extern inline verilog_assertt &to_verilog_assert(exprt &expr)
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

extern inline const verilog_assumet &to_verilog_assume(const exprt &expr)
{
  assert(expr.id()==ID_assume && expr.operands().size()==2);
  return static_cast<const verilog_assumet &>(expr);
}

extern inline verilog_assumet &to_verilog_assume(exprt &expr)
{
  assert(expr.id()==ID_assume && expr.operands().size()==2);
  return static_cast<verilog_assumet &>(expr);
}

#endif
