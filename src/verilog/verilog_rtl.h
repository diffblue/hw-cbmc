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

/// The register-transfer level (RTL) representation of a Verilog
/// module: a map from identifiers to a map from slices to the
/// definition of the slice. This representation follows type
/// checking and elaboration, and precedes synthesis.
class verilog_rtlt
{
public:
  using slice_mapt = std::map<verilog_rtl_slicet, verilog_rtl_definitiont>;
  using identifier_mapt = std::map<irep_idt, slice_mapt>;

  identifier_mapt identifier_map;

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
