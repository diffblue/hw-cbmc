/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_VHDL_PARSE_TREE_H
#define CPROVER_VHDL_PARSE_TREE_H

#include <util/irep.h>
#include <util/source_location.h>
#include <util/string_hash.h>

#include <list>
#include <set>

class vhdl_parse_treet
{
public:
  struct itemt : public irept
  {
  public:
    irep_idt get_item_type() const
    {
      return get("item_type");
    }
    void set_item_type(const irep_idt &item_type)
    {
      set("item_type", item_type);
    }

    void set_name(const irept &name)
    {
      set(ID_name, name);
    }
    irept get_name() const
    {
      return find(ID_name);
    }

    void show(std::ostream &out) const;
    static std::string pretty_name(const irept &);
    std::string get_pretty_name() const
    {
      return pretty_name(get_name());
    }

    /// Basic identifiers are case insensitive (IEEE 1076-2008 15.4.2),
    /// extended identifiers are not (15.4.3); this returns the lower-case
    /// version of a basic identifier, and extended identifiers unchanged
    static irep_idt to_lower(const irep_idt &);

    /// the name of the design unit, in lower case
    irep_idt get_identifier() const
    {
      return to_lower(get_pretty_name());
    }

    /// for architectures, the name of the entity, in lower case
    irep_idt get_entity_identifier() const
    {
      return to_lower(pretty_name(find(ID_entity)));
    }

    bool is_architecture() const
    {
      return get("item_type") == "architecture";
    }
    bool is_entity() const
    {
      return get("item_type") == "entity";
    }
    bool is_use() const
    {
      return get("item_type") == "use";
    }
    bool is_library() const
    {
      return get("item_type") == "library";
    }
    bool is_package() const
    {
      return get("item_type") == "package";
    }
    bool is_package_body() const
    {
      return get("item_type") == "package_body";
    }

    const source_locationt &source_location() const
    {
      return static_cast<const source_locationt &>(find(ID_C_source_location));
    }
  };

  typedef std::list<itemt> itemst;
  itemst items;

  void clear()
  {
    items.clear();
  }

  void swap(vhdl_parse_treet &parse_tree)
  {
    parse_tree.items.swap(items);
  }

  void show(std::ostream &out) const;
};

#endif
