/*******************************************************************\

Module: FastPPA whole-design graph estimator

Author: Kiro

\*******************************************************************/

#ifndef CPROVER_FASTPPA_ESTIMATE_H
#define CPROVER_FASTPPA_ESTIMATE_H

#include <util/mathematical_expr.h>
#include <util/source_location.h>
#include <util/std_expr.h>

#include <vector>

class cost_tablet;
class message_handlert;
class namespacet;

/// A path through the logic, from a register or input to a register or
/// output, ordered from start to end.
struct critical_patht
{
  irep_idt endpoint;
  bool endpoint_is_register = false;
  double arrival_ps = 0;

  struct stept
  {
    irep_idt operation; // e.g. "+"; "input" or "register" at the start
    irep_idt name;      // the input or register at the start
    std::size_t width = 0;
    double arrival_ps = 0;
    source_locationt source_location;
  };

  std::vector<stept> steps;
};

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
  /// the paths to each register and output, the slowest first
  std::vector<critical_patht> critical_paths;
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
