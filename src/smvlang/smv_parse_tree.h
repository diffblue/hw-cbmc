/*******************************************************************\

Module: SMV Parse Tree

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SMV_PARSE_TREE_H
#define CPROVER_SMV_PARSE_TREE_H

#include <util/std_expr.h>
#include <util/string_hash.h>

#include <unordered_map>
#include <unordered_set>

class smv_parse_treet
{
public:

  struct mc_vart
  {
    typedef enum { UNKNOWN, DECLARED, DEFINED, ARGUMENT } var_classt;
    var_classt var_class;
    typet type;
    irep_idt identifier;
    
    mc_vart():var_class(UNKNOWN), type(typet(ID_bool))
    {
    }
  };
   
  typedef std::unordered_map<irep_idt, mc_vart, irep_id_hash> mc_varst;
  typedef std::unordered_set<irep_idt, irep_id_hash> enum_sett;

  struct modulet
  {
    irep_idt name, base_name;
    std::list<irep_idt> parameters;

    struct itemt
    {
      enum item_typet
      {
        ASSIGN_CURRENT,
        ASSIGN_INIT,
        ASSIGN_NEXT,
        CTLSPEC,
        DEFINE,
        ENUM,
        FAIRNESS,
        INIT,
        INVAR,
        IVAR,
        LTLSPEC,
        TRANS,
        VAR
      };

      itemt(item_typet __item_type, exprt __expr, source_locationt __location)
        : item_type(__item_type),
          expr(std::move(__expr)),
          location(std::move(__location))
      {
      }

      itemt(
        item_typet __item_type,
        irep_idt __name,
        exprt __expr,
        source_locationt __location)
        : item_type(__item_type),
          name(__name),
          expr(std::move(__expr)),
          location(std::move(__location))
      {
      }

      friend std::string to_string(item_typet i);
      
      item_typet item_type;
      std::optional<irep_idt> name;
      exprt expr;
      source_locationt location;

      bool is_assign_current() const
      {
        return item_type == ASSIGN_CURRENT;
      }

      bool is_assign_init() const
      {
        return item_type == ASSIGN_INIT;
      }

      bool is_assign_next() const
      {
        return item_type == ASSIGN_NEXT;
      }

      bool is_ctlspec() const
      {
        return item_type == CTLSPEC;
      }

      bool is_ltlspec() const
      {
        return item_type == LTLSPEC;
      }

      bool is_define() const
      {
        return item_type==DEFINE;
      }
      
      bool is_invar() const
      {
        return item_type==INVAR;
      }
      
      bool is_trans() const
      {
        return item_type==TRANS;
      }
      
      bool is_init() const
      {
        return item_type==INIT;
      }

      bool is_enum() const
      {
        return item_type == ENUM;
      }

      bool is_ivar() const
      {
        return item_type == IVAR;
      }

      bool is_var() const
      {
        return item_type == VAR;
      }

      // for ASSIGN_CURRENT, ASSIGN_INIT, ASSIGN_NEXT, DEFINE
      const equal_exprt &equal_expr() const
      {
        PRECONDITION(
          is_assign_current() || is_assign_init() || is_assign_next() ||
          is_define());
        return to_equal_expr(expr);
      }

      equal_exprt &equal_expr()
      {
        PRECONDITION(
          is_assign_current() || is_assign_init() || is_assign_next() ||
          is_define());
        return to_equal_expr(expr);
      }
    };
    
    typedef std::list<itemt> item_listt;
    item_listt items;

    void add_assign_current(exprt lhs, exprt rhs)
    {
      items.emplace_back(
        itemt::ASSIGN_CURRENT,
        binary_exprt{std::move(lhs), ID_equal, std::move(rhs)},
        source_locationt::nil());
    }

    void add_assign_init(exprt lhs, exprt rhs)
    {
      items.emplace_back(
        itemt::ASSIGN_INIT,
        binary_exprt{std::move(lhs), ID_equal, std::move(rhs)},
        source_locationt::nil());
    }

    void add_assign_next(exprt lhs, exprt rhs)
    {
      items.emplace_back(
        itemt::ASSIGN_NEXT,
        binary_exprt{std::move(lhs), ID_equal, std::move(rhs)},
        source_locationt::nil());
    }

    void add_invar(exprt expr)
    {
      items.emplace_back(
        itemt::INVAR, std::move(expr), source_locationt::nil());
    }

    void add_define(exprt lhs, exprt rhs)
    {
      items.emplace_back(
        itemt::DEFINE,
        binary_exprt{std::move(lhs), ID_equal, std::move(rhs)},
        source_locationt::nil());
    }

    void add_fairness(exprt expr)
    {
      items.emplace_back(
        itemt::FAIRNESS, std::move(expr), source_locationt::nil());
    }

    void add_init(exprt expr)
    {
      items.emplace_back(itemt::INIT, std::move(expr), source_locationt::nil());
    }

    void add_trans(exprt expr)
    {
      items.emplace_back(
        itemt::TRANS, std::move(expr), source_locationt::nil());
    }

    void add_invar(exprt expr, source_locationt location)
    {
      items.emplace_back(itemt::INVAR, std::move(expr), location);
    }

    void add_ctlspec(exprt expr, source_locationt location)
    {
      items.emplace_back(itemt::CTLSPEC, std::move(expr), std::move(location));
    }

    void add_ctlspec(irep_idt name, exprt expr, source_locationt location)
    {
      items.emplace_back(
        itemt::CTLSPEC, name, std::move(expr), std::move(location));
    }

    void add_ltlspec(exprt expr, source_locationt location)
    {
      items.emplace_back(itemt::LTLSPEC, std::move(expr), location);
    }

    void add_ltlspec(irep_idt name, exprt expr, source_locationt location)
    {
      items.emplace_back(itemt::LTLSPEC, name, std::move(expr), location);
    }

    void add_define(exprt expr, source_locationt location)
    {
      items.emplace_back(itemt::DEFINE, std::move(expr), std::move(location));
    }

    void add_fairness(exprt expr, source_locationt location)
    {
      items.emplace_back(itemt::FAIRNESS, std::move(expr), std::move(location));
    }

    void add_init(exprt expr, source_locationt location)
    {
      items.emplace_back(itemt::INIT, std::move(expr), std::move(location));
    }

    void add_trans(exprt expr, source_locationt location)
    {
      items.emplace_back(itemt::TRANS, std::move(expr), std::move(location));
    }

    void add_ivar(exprt expr, typet type)
    {
      expr.type() = std::move(type);
      auto location = expr.source_location();
      items.emplace_back(itemt::IVAR, std::move(expr), std::move(location));
    }

    void add_var(exprt expr, typet type)
    {
      expr.type() = std::move(type);
      auto location = expr.source_location();
      items.emplace_back(itemt::VAR, std::move(expr), std::move(location));
    }

    void add_enum(exprt expr)
    {
      auto location = expr.source_location();
      items.emplace_back(itemt::ENUM, std::move(expr), std::move(location));
    }

    mc_varst vars;
    enum_sett enum_set;
  };
   
  typedef std::unordered_map<irep_idt, modulet, irep_id_hash> modulest;
  
  modulest modules;
  
  void swap(smv_parse_treet &smv_parse_tree);
  void clear();
};

#define forall_item_list(it, expr) \
  for(smv_parse_treet::modulet::item_listt::const_iterator it=(expr).begin(); \
      it!=(expr).end(); it++)
#endif
