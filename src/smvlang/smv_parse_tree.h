/*******************************************************************\

Module: SMV Parse Tree

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SMV_PARSE_TREE_H
#define CPROVER_SMV_PARSE_TREE_H

#include <unordered_set>
#include <unordered_map>

#include <util/string_hash.h>
#include <util/expr.h>

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
    
    struct itemt
    {
      enum item_typet
      {
        CTLSPEC,
        LTLSPEC,
        INIT,
        TRANS,
        DEFINE,
        INVAR,
        FAIRNESS
      };

      friend std::string to_string(item_typet i);
      
      item_typet item_type;
      exprt expr;
      source_locationt location;

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
      
    };
    
    typedef std::list<itemt> item_listt;
    item_listt items;
    
    void add_item(
      itemt::item_typet item_type,
      const exprt &expr,
      const source_locationt &location)
    {
      items.push_back(itemt());
      items.back().item_type=item_type;
      items.back().expr=expr;
      items.back().location=location;
    }
    
    void add_invar(const exprt &expr)
    {
      add_item(itemt::INVAR, expr, source_locationt::nil());
    }

    void add_ctlspec(const exprt &expr)
    {
      add_item(itemt::CTLSPEC, expr, source_locationt::nil());
    }

    void add_ltlspec(const exprt &expr)
    {
      add_item(itemt::LTLSPEC, expr, source_locationt::nil());
    }

    void add_define(const exprt &expr)
    {
      add_item(itemt::DEFINE, expr, source_locationt::nil());
    }
    
    void add_fairness(const exprt &expr)
    {
      add_item(itemt::FAIRNESS, expr, source_locationt::nil());
    }
    
    void add_init(const exprt &expr)
    {
      add_item(itemt::INIT, expr, source_locationt::nil());
    }
    
    void add_trans(const exprt &expr)
    {
      add_item(itemt::TRANS, expr, source_locationt::nil());
    }
    
    void add_invar(const exprt &expr, const source_locationt &location)
    {
      add_item(itemt::INVAR, expr, location);
    }

    void add_ctlspec(const exprt &expr, const source_locationt &location)
    {
      add_item(itemt::CTLSPEC, expr, location);
    }

    void add_ltlspec(const exprt &expr, const source_locationt &location)
    {
      add_item(itemt::LTLSPEC, expr, location);
    }
    
    void add_define(const exprt &expr, const source_locationt &location)
    {
      add_item(itemt::DEFINE, expr, location);
    }
    
    void add_fairness(const exprt &expr, const source_locationt &location)
    {
      add_item(itemt::FAIRNESS, expr, location);
    }
    
    void add_init(const exprt &expr, const source_locationt &location)
    {
      add_item(itemt::INIT, expr, location);
    }
    
    void add_trans(const exprt &expr, const source_locationt &location)
    {
      add_item(itemt::TRANS, expr, location);
    }
    
    mc_varst vars;
    enum_sett enum_set;

    std::list<irep_idt> ports;
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
