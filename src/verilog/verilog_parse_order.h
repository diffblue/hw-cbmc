/*******************************************************************\

Module: Verilog Parse Order

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Verilog Parse Order

#ifndef CPROVER_VERILOG_VERILOG_PARSE_ORDER_H
#define CPROVER_VERILOG_VERILOG_PARSE_ORDER_H

#include <util/irep.h>

#include "verilog_standard.h"

#include <cstddef>
#include <iosfwd>
#include <set>
#include <vector>

/// The package declarations and the references to packages found in one
/// (preprocessed) Verilog input file.
struct verilog_package_usaget
{
  /// the packages declared by the file
  std::set<irep_idt> declares;

  /// the packages referenced by the file, e.g., in an import
  std::set<irep_idt> references;
};

/// Scan the given preprocessed Verilog text for package declarations and for
/// references to packages. This uses the scanner only, i.e., no parse tree is
/// built and no scopes are created. Any scanner error is ignored; it is
/// reported when the file is parsed.
verilog_package_usaget
verilog_scan_package_usage(std::istream &, verilog_standardt);

/// Given the package usage of the input files, in the order in which they
/// were given, return the order in which the files are to be parsed, such
/// that the file declaring a package is parsed before the files that
/// reference that package. IEEE 1800-2017 26.3 requires that a package is
/// compiled before it is referenced, but says nothing about the order of the
/// input files. Files without such a dependency retain their relative order.
/// Dependency cycles, which are illegal, are broken arbitrarily; the parser
/// then reports the offending reference.
std::vector<std::size_t>
verilog_parse_order(const std::vector<verilog_package_usaget> &);

#endif // CPROVER_VERILOG_VERILOG_PARSE_ORDER_H
