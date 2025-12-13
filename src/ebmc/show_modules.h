/*******************************************************************\

Module: Show Modules

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_EBMC_SHOW_MODULES_H
#define CPROVER_EBMC_SHOW_MODULES_H

#include <util/source_location.h>

#include <iosfwd>
#include <list>
#include <string>

class symbol_table_baset;

class show_modulest
{
public:
  struct modulet
  {
    modulet(
      irep_idt _identifier,
      irep_idt _display_name,
      irep_idt _mode,
      source_locationt _source_location)
      : identifier(_identifier),
        display_name(_display_name),
        mode(_mode),
        source_location(std::move(_source_location))
    {
    }

    irep_idt identifier, display_name, mode;
    source_locationt source_location;
  };

  using modulest = std::list<modulet>;
  modulest modules;

  void plain_text(std::ostream &) const;
  void xml(std::ostream &) const;
  void json(std::ostream &) const;

  static show_modulest from_symbol_table(const symbol_table_baset &);
};

#endif
