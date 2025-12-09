/*******************************************************************\

Module: SMV Parse Tree

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SMV_PARSE_TREE_H
#define CPROVER_SMV_PARSE_TREE_H

#include <util/std_expr.h>
#include <util/string_hash.h>

#include <iosfwd>
#include <unordered_map>
#include <unordered_set>

class smv_parse_treet
{
public:
  smv_parse_treet() = default;
  smv_parse_treet(smv_parse_treet &&) = default;

  // don't copy, contains pointers
  smv_parse_treet(const smv_parse_treet &) = delete;

  typedef std::unordered_set<irep_idt, irep_id_hash> enum_sett;

  struct modulet
  {
    irep_idt name, base_name;
    std::vector<irep_idt> parameters;

    struct elementt
    {
      enum element_typet
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

      elementt(
        element_typet __element_type,
        exprt __expr,
        source_locationt __location)
        : element_type(__element_type),
          expr(std::move(__expr)),
          location(std::move(__location))
      {
      }

      elementt(
        element_typet __element_type,
        irep_idt __name,
        exprt __expr,
        source_locationt __location)
        : element_type(__element_type),
          name(__name),
          expr(std::move(__expr)),
          location(std::move(__location))
      {
      }

      friend std::string to_string(element_typet i);

      element_typet element_type;
      std::optional<irep_idt> name;
      exprt expr;
      source_locationt location;

      bool is_assign_current() const
      {
        return element_type == ASSIGN_CURRENT;
      }

      bool is_assign_init() const
      {
        return element_type == ASSIGN_INIT;
      }

      bool is_assign_next() const
      {
        return element_type == ASSIGN_NEXT;
      }

      bool is_ctlspec() const
      {
        return element_type == CTLSPEC;
      }

      bool is_ltlspec() const
      {
        return element_type == LTLSPEC;
      }

      bool is_define() const
      {
        return element_type == DEFINE;
      }
      
      bool is_invar() const
      {
        return element_type == INVAR;
      }
      
      bool is_trans() const
      {
        return element_type == TRANS;
      }
      
      bool is_init() const
      {
        return element_type == INIT;
      }

      bool is_enum() const
      {
        return element_type == ENUM;
      }

      bool is_ivar() const
      {
        return element_type == IVAR;
      }

      bool is_var() const
      {
        return element_type == VAR;
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

      void show(std::ostream &) const;
    };

    typedef std::list<elementt> element_listt;
    element_listt elements;

    void add_assign_current(exprt lhs, exprt rhs)
    {
      elements.emplace_back(
        elementt::ASSIGN_CURRENT,
        binary_exprt{std::move(lhs), ID_equal, std::move(rhs)},
        source_locationt::nil());
    }

    void add_assign_init(exprt lhs, exprt rhs)
    {
      elements.emplace_back(
        elementt::ASSIGN_INIT,
        binary_exprt{std::move(lhs), ID_equal, std::move(rhs)},
        source_locationt::nil());
    }

    void add_assign_next(exprt lhs, exprt rhs)
    {
      elements.emplace_back(
        elementt::ASSIGN_NEXT,
        binary_exprt{std::move(lhs), ID_equal, std::move(rhs)},
        source_locationt::nil());
    }

    void add_invar(exprt expr)
    {
      elements.emplace_back(
        elementt::INVAR, std::move(expr), source_locationt::nil());
    }

    void add_define(exprt lhs, exprt rhs)
    {
      elements.emplace_back(
        elementt::DEFINE,
        binary_exprt{std::move(lhs), ID_equal, std::move(rhs)},
        source_locationt::nil());
    }

    void add_fairness(exprt expr)
    {
      elements.emplace_back(
        elementt::FAIRNESS, std::move(expr), source_locationt::nil());
    }

    void add_init(exprt expr)
    {
      elements.emplace_back(
        elementt::INIT, std::move(expr), source_locationt::nil());
    }

    void add_trans(exprt expr)
    {
      elements.emplace_back(
        elementt::TRANS, std::move(expr), source_locationt::nil());
    }

    void add_invar(exprt expr, source_locationt location)
    {
      elements.emplace_back(elementt::INVAR, std::move(expr), location);
    }

    void add_ctlspec(exprt expr, source_locationt location)
    {
      elements.emplace_back(
        elementt::CTLSPEC, std::move(expr), std::move(location));
    }

    void add_ctlspec(irep_idt name, exprt expr, source_locationt location)
    {
      elements.emplace_back(
        elementt::CTLSPEC, name, std::move(expr), std::move(location));
    }

    void add_ltlspec(exprt expr, source_locationt location)
    {
      elements.emplace_back(elementt::LTLSPEC, std::move(expr), location);
    }

    void add_ltlspec(irep_idt name, exprt expr, source_locationt location)
    {
      elements.emplace_back(elementt::LTLSPEC, name, std::move(expr), location);
    }

    void add_define(exprt expr, source_locationt location)
    {
      elements.emplace_back(
        elementt::DEFINE, std::move(expr), std::move(location));
    }

    void add_fairness(exprt expr, source_locationt location)
    {
      elements.emplace_back(
        elementt::FAIRNESS, std::move(expr), std::move(location));
    }

    void add_init(exprt expr, source_locationt location)
    {
      elements.emplace_back(
        elementt::INIT, std::move(expr), std::move(location));
    }

    void add_trans(exprt expr, source_locationt location)
    {
      elements.emplace_back(
        elementt::TRANS, std::move(expr), std::move(location));
    }

    void add_ivar(exprt expr, typet type)
    {
      expr.type() = std::move(type);
      auto location = expr.source_location();
      elements.emplace_back(
        elementt::IVAR, std::move(expr), std::move(location));
    }

    void add_var(exprt expr, typet type)
    {
      expr.type() = std::move(type);
      auto location = expr.source_location();
      elements.emplace_back(
        elementt::VAR, std::move(expr), std::move(location));
    }

    void add_enum(exprt expr)
    {
      auto location = expr.source_location();
      elements.emplace_back(
        elementt::ENUM, std::move(expr), std::move(location));
    }
  };

  using module_listt = std::list<modulet>;
  module_listt module_list;

  using module_mapt =
    std::unordered_map<irep_idt, module_listt::iterator, irep_id_hash>;
  module_mapt module_map;

  // enums are global
  enum_sett enum_set;

  void swap(smv_parse_treet &);
  void clear();

  void show(std::ostream &) const;
};

#endif
