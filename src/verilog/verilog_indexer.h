/*******************************************************************\

Module: Verilog Indexer

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef VERILOG_INDEXER_H
#define VERILOG_INDEXER_H

#include <iosfwd>
#include <unordered_map>

// just for irep_idt
#include <util/irep.h>

/// Verilog allows modules, classes, packages, interfaces,
/// tasks, functions, wires to be used before they are declared,
/// which makes typing identifier tokens difficult.
/// This maps identifiers to their kind and file,
/// for the benefit of parsing/typechecking.
class verilog_indexert
{
public:
  struct idt
  {
    using kindt = enum { MODULE, PACKAGE, CLASS, TYPEDEF, INSTANCE };
    kindt kind;
    irep_idt file_name;
  };

  // The keys are Verilog hierarchical identifiers
  // without Verilog:: prefix, as this is Verilog only.
  using id_mapt = std::unordered_map<irep_idt, idt>;
  id_mapt id_map;

  // a lookup helper
  std::optional<const idt &> operator[](const irep_idt &) const;

  /// index the given file
  void operator()(const irep_idt &file_name);

protected:
  struct parsert
  {
    irep_idt file_name;

    // grammar rules
    void rDescription();
  };

  std::string preprocess(const std::string &file_name);
};

#endif // VERILOG_INDEXER_H
