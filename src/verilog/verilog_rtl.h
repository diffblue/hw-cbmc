/*******************************************************************\

Module: Verilog Register-Transfer Level Representation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_VERILOG_VERILOG_RTL_H
#define CPROVER_VERILOG_VERILOG_RTL_H

#include <util/expr.h>
#include <util/invariant.h>
#include <util/mp_arith.h>

#include "verilog_standard.h"

#include <iosfwd>
#include <map>
#include <set>
#include <vector>

class message_handlert;
class namespacet;
class symbol_table_baset;

/// A contiguous range of bits of an identifier, given as
/// zero-based bit indices [lower, higher], both inclusive.
class verilog_rtl_slicet
{
public:
  verilog_rtl_slicet(mp_integer _lower, mp_integer _higher)
    : lower(std::move(_lower)), higher(std::move(_higher))
  {
    PRECONDITION(lower <= higher);
  }

  mp_integer lower, higher;

  mp_integer width() const
  {
    return higher - lower + 1;
  }

  /// do the two slices share at least one bit?
  bool overlaps(const verilog_rtl_slicet &other) const
  {
    return lower <= other.higher && other.lower <= higher;
  }

  bool operator<(const verilog_rtl_slicet &other) const
  {
    if(lower != other.lower)
      return lower < other.lower;
    else
      return higher < other.higher;
  }

  bool operator==(const verilog_rtl_slicet &other) const
  {
    return lower == other.lower && higher == other.higher;
  }
};

/// The definition of a slice of an identifier: the slice is either
/// state-holding (a register) or a wire, together with the defining
/// expression.
class verilog_rtl_definitiont
{
public:
  enum class kindt
  {
    STATE_HOLDING,
    WIRE
  };

  kindt kind;

  /// For state-holding slices, the value of the slice in the *next*
  /// state; for wires, the value of the slice in the *current* state.
  exprt value;

  verilog_rtl_definitiont(kindt _kind, exprt _value)
    : kind(_kind), value(std::move(_value))
  {
  }

  bool is_state_holding() const
  {
    return kind == kindt::STATE_HOLDING;
  }

  bool is_wire() const
  {
    return kind == kindt::WIRE;
  }
};

/// An assert, assume or cover property, with an optional label.
class verilog_rtl_propertyt
{
public:
  enum class kindt
  {
    ASSERT,
    ASSUME,
    COVER
  };

  /// the context in which the property occurs
  enum class contextt
  {
    MODULE_LEVEL,
    ALWAYS,
    INITIAL
  };

  kindt kind;
  contextt context;

  /// the full identifier created by the type checker
  irep_idt identifier;

  /// the label of the property, or empty if none was given
  irep_idt label;

  /// the condition, with values substituted and function
  /// calls expanded
  exprt condition;

  /// the condition as written in the source, for display
  exprt source_condition;

  /// distinguishes 'cover sequence' from 'cover property'
  bool is_sequence = false;

  verilog_rtl_propertyt(
    kindt _kind,
    contextt _context,
    irep_idt _identifier,
    irep_idt _label,
    exprt _condition,
    exprt _source_condition)
    : kind(_kind),
      context(_context),
      identifier(std::move(_identifier)),
      label(std::move(_label)),
      condition(std::move(_condition)),
      source_condition(std::move(_source_condition))
  {
  }

  bool is_assert() const
  {
    return kind == kindt::ASSERT;
  }

  bool is_assume() const
  {
    return kind == kindt::ASSUME;
  }

  bool is_cover() const
  {
    return kind == kindt::COVER;
  }
};

/// The register-transfer level (RTL) representation of a Verilog
/// module: a map from identifiers to a map from slices to the
/// definition of the slice, the initial values, further constraints,
/// and the assert, assume and cover properties of the module.
/// Module instances are included recursively. This representation
/// follows type checking and elaboration, and precedes synthesis.
class verilog_rtlt
{
public:
  using slice_mapt = std::map<verilog_rtl_slicet, verilog_rtl_definitiont>;
  using identifier_mapt = std::map<irep_idt, slice_mapt>;
  using slice_value_mapt = std::map<verilog_rtl_slicet, exprt>;

  identifier_mapt identifier_map;

  /// the declared state-holding variables, including those
  /// that are not assigned; unassigned variables hold their value
  std::set<irep_idt> variables;

  /// identifiers that are forced to a value, e.g. by a port
  /// connection; these become wires
  std::set<irep_idt> forced;

  /// the initial values, from initial constructs and variable
  /// declarations with an initializer
  std::map<irep_idt, slice_value_mapt> initial_values;

  /// Boolean constraints that hold in every state,
  /// e.g. from primitive gates
  std::vector<exprt> constraints;

  /// the properties, in the order in which they appear in the module
  std::vector<verilog_rtl_propertyt> properties;

  void output(const namespacet &, std::ostream &) const;
};

/// Construct the RTL representation of the given type-checked
/// module. Throws ebmc_errort on failure.
verilog_rtlt verilog_rtl(
  const symbol_table_baset &,
  const irep_idt &module_identifier,
  verilog_standardt,
  message_handlert &);

#endif // CPROVER_VERILOG_VERILOG_RTL_H
