/*******************************************************************\

Module: FastPPA whole-design graph estimator

Author: Kiro

\*******************************************************************/

#ifndef CPROVER_FASTPPA_ESTIMATE_H
#define CPROVER_FASTPPA_ESTIMATE_H

#include <util/mathematical_expr.h>
#include <util/std_expr.h>

#include <vector>

class cost_tablet;
class message_handlert;
class namespacet;

struct estimation_resultt
{
  double total_area_um2 = 0;
  double register_area_um2 = 0;
  double combinational_area_um2 = 0;
  double critical_path_ps = 0;
  /// switching energy per clock cycle and unit of toggle rate
  double data_energy_fj = 0;
  /// energy per clock cycle of the clock pins of the registers
  double clock_energy_fj = 0;
  double leakage_uw = 0;
  std::size_t register_bits = 0;
  std::size_t combinational_depth = 0;
  std::size_t operator_count = 0;
};

/// Estimates area and delay of the hardware described by a transition
/// system. The state constraints of \p trans define wires and outputs,
/// and its transition constraints the next-state functions of the
/// registers in \p state_vars. Only logic that reaches one of \p outputs,
/// directly or through registers, is costed.
estimation_resultt estimate(
  const transt &trans,
  const std::vector<symbol_exprt> &state_vars,
  const std::vector<symbol_exprt> &outputs,
  const namespacet &,
  const cost_tablet &,
  message_handlert &);

#endif // CPROVER_FASTPPA_ESTIMATE_H
