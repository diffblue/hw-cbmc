/*******************************************************************\

Module: VHDL Standard

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

#ifndef CPROVER_VHDL_VHDL_STANDARD_H
#define CPROVER_VHDL_VHDL_STANDARD_H

#include <optional>
#include <string>

/// The revisions of IEEE 1076 that differ in a way the front-end
/// distinguishes. The language accepted is that of IEEE 1076-2008
/// throughout; the standard selects the semantics of the constructs
/// that changed between revisions.
enum class vhdl_standardt
{
  VHDL87,
  VHDL93,
  VHDL2008
};

/// the default when --vhdl-std is not given
constexpr vhdl_standardt default_vhdl_standard = vhdl_standardt::VHDL2008;

/// The standard for the argument of --vhdl-std: "87", "93" or "2008".
/// Returns nothing for any other string.
std::optional<vhdl_standardt> vhdl_standard_from_string(const std::string &);

/// e.g., "1076-2008"
std::string as_string(vhdl_standardt);

#endif // CPROVER_VHDL_VHDL_STANDARD_H
