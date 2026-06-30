/*******************************************************************\

Module: Technology Database for FastPPA Estimation

Author: Kiro

\*******************************************************************/

#include "technology_db.h"

#include "fastppa_error.h"

#include <map>

// Reference: NanGate 45nm Open Cell Library approximate values.
// All costs scale from this baseline using per-node factors.

struct process_scalest
{
  double area;
  double delay;
  double energy;
  double leakage;
  double wire_cap;
};

static const std::map<std::string, process_scalest> process_table = {
  {"3nm", {0.012, 0.15, 0.025, 8.0, 0.5}},
  {"7nm", {0.034, 0.25, 0.05, 4.0, 0.4}},
  {"14nm", {0.097, 0.45, 0.15, 2.0, 0.35}},
  {"28nm", {0.39, 0.7, 0.4, 1.2, 0.25}},
  {"45nm", {1.0, 1.0, 1.0, 1.0, 0.2}},
  {"65nm", {2.1, 1.4, 2.0, 0.7, 0.15}},
  {"90nm", {4.0, 2.0, 4.0, 0.5, 0.12}},
  {"130nm", {8.4, 2.9, 8.0, 0.3, 0.1}},
};

technology_dbt::technology_dbt(const std::string &process_name)
  : process(process_name)
{
  auto it = process_table.find(process_name);
  if(it == process_table.end())
    throw fastppa_errort{} << "unknown process node: " << process_name;
  scale_area = it->second.area;
  scale_delay = it->second.delay;
  scale_energy = it->second.energy;
  scale_leakage = it->second.leakage;
  wire_delay_cap = it->second.wire_cap;
}

// Base costs at 45nm per bit for various operators.
// area: µm²/bit, delay: ps (total, width-dependent), energy: fJ/bit
operator_costt
technology_dbt::operator_cost(const irep_idt &op, std::size_t width) const
{
  double n = static_cast<double>(width);
  if(n < 1)
    n = 1;

  double area_per_bit = 0;
  double delay = 0;
  double energy_per_bit = 0;

  // Arithmetic.
  //
  // Calibrated against real synthesis (Yosys 0.64 + ABC, NanGate45
  // typical liberty) of per-operator, multi-width benchmarks
  // (benchmarking/fastppa_scaling/{adder,mult,shift,cmp}_{8,16,32,64,128}.sv),
  // with the register contribution measured directly from synthesized
  // DFF_X1 cell counts and subtracted out before fitting.
  if(op == ID_plus || op == ID_minus)
  {
    // Generic synthesis (no explicit CLA hint) measured as linear in
    // width, not log(n): real delay went 0.24/0.54/1.11/2.18/4.30 ns for
    // n=8/16/32/64/128, i.e. ~34 ps/bit with negligible fixed overhead.
    area_per_bit = 6.0;
    delay = 34.0 * n;
    energy_per_bit = 3.0;
  }
  else if(op == ID_mult)
  {
    // Tree multiplier: area ~quadratic, delay sub-linear in width
    // (measured exponent ~0.86 over n=16..128 output-width range).
    area_per_bit = 1.6 * n;
    delay = 71.0 * std::pow(n, 0.86);
    energy_per_bit = 1.5 * n;
  }
  else if(op == ID_div || op == ID_mod)
  {
    // Iterative (single-cycle, fully unrolled) divider: calibrated against
    // real synthesis of benchmarking/fastppa_scaling/{div,mod}_{8,16,32,64}.sv
    // -- area ~quadratic (measured exponent ~1.98), delay also close to
    // quadratic (measured exponent ~1.89), not the previous linear guess
    // (which underestimated a 32-bit divider's real 27.7 ns critical path
    // by ~8x). div and mod measured separately but converge to within ~2%
    // of each other by n=64 (real synthesis shares the subtract/compare/
    // shift array between quotient and remainder), so one shared formula
    // is fit to both. energy_per_bit is scaled from area_per_bit using the
    // same ratio as before, not independently measured.
    area_per_bit = 4.34 * n;
    delay = 38.3 * std::pow(n, 1.89);
    energy_per_bit = 2.7 * n;
  }
  // Shifts
  else if(op == ID_shl || op == ID_lshr || op == ID_ashr)
  {
    // Barrel shifter: real area scales slightly faster than n*log(n)
    // (measured exponent ~1.32); real delay has both a logic-depth term
    // and a width/fanout term, not log(n) alone.
    area_per_bit = 2.51 * std::pow(n, 0.32);
    delay = 54.0 * std::log2(n) + 1.3 * n;
    energy_per_bit = 0.5;
  }
  // Bitwise logic (single gate level)
  else if(
    op == ID_bitand || op == ID_bitor || op == ID_bitxor || op == ID_bitnot ||
    op == ID_not || op == ID_bitnand || op == ID_bitnor || op == ID_bitxnor)
  {
    area_per_bit = 1.5;
    delay = 15.0;
    energy_per_bit = 0.3;
  }
  // Comparison
  else if(
    op == ID_equal || op == ID_notequal || op == ID_lt || op == ID_le ||
    op == ID_gt || op == ID_ge)
  {
    // Comparator: area ~linear in width (measured ~3.8 um2/bit), delay
    // O(log n) with negligible fixed overhead (measured ~67.5 ps/level).
    area_per_bit = 3.8;
    delay = 67.5 * std::log2(n);
    energy_per_bit = 1.0;
  }
  // MUX / if-then-else
  else if(op == ID_if || op == ID_cond)
  {
    area_per_bit = 3.0;
    delay = 25.0;
    energy_per_bit = 0.8;
  }
  // Concatenation, type casts — no hardware cost
  else if(
    op == ID_concatenation || op == ID_extractbits || op == ID_extractbit ||
    op == ID_typecast || op == ID_zero_extend)
  {
    area_per_bit = 0;
    delay = 0;
    energy_per_bit = 0;
  }
  // Reduction operators
  else if(
    op == ID_reduction_and || op == ID_reduction_or || op == ID_reduction_xor)
  {
    area_per_bit = 1.0;
    delay = 10.0 * std::log2(n);
    energy_per_bit = 0.3;
  }
  // Unary minus (two's complement): structurally one adder, same scaling
  // as plus/minus above.
  else if(op == ID_unary_minus)
  {
    area_per_bit = 5.0;
    delay = 34.0 * n;
    energy_per_bit = 1.5;
  }
  // Default: treat as simple logic
  else
  {
    area_per_bit = 2.0;
    delay = 20.0;
    energy_per_bit = 0.5;
  }

  operator_costt cost;
  cost.area_um2 = area_per_bit * n * scale_area;
  cost.delay_ps = delay * scale_delay;
  cost.energy_fj = energy_per_bit * n * scale_energy;
  return cost;
}

operator_costt technology_dbt::register_cost(std::size_t width) const
{
  double n = static_cast<double>(width);
  // DFF: 4.52 µm²/bit at 45nm (NanGate45 DFF_X1, measured), setup ~50 ps
  operator_costt cost;
  cost.area_um2 = 4.52 * n * scale_area;
  cost.delay_ps = 50.0 * scale_delay;
  cost.energy_fj = 2.0 * n * scale_energy;
  return cost;
}

operator_costt
technology_dbt::mux_cost(std::size_t width, std::size_t inputs) const
{
  double n = static_cast<double>(width);
  double levels = std::ceil(std::log2(static_cast<double>(inputs)));
  operator_costt cost;
  cost.area_um2 = 3.0 * n * levels * scale_area;
  cost.delay_ps = 25.0 * levels * scale_delay;
  cost.energy_fj = 0.8 * n * levels * scale_energy;
  return cost;
}

operator_costt technology_dbt::constant_mult_cost(
  std::size_t width,
  std::size_t constant_bits) const
{
  // Multiply by constant: implemented as shift-add network
  // Cost ~ popcount(constant) adders, each width-bit
  double n = static_cast<double>(width);
  double adds = static_cast<double>(constant_bits > 0 ? constant_bits : 1);
  operator_costt cost;
  cost.area_um2 = 5.0 * n * adds * scale_area;
  cost.delay_ps =
    (50.0 + 30.0 * std::log2(n)) * std::ceil(std::log2(adds + 1)) * scale_delay;
  cost.energy_fj = 1.5 * n * adds * scale_energy;
  return cost;
}

operator_costt technology_dbt::index_cost(
  std::size_t element_width,
  std::size_t array_size) const
{
  // Array read: decoder + mux tree, equivalent to an array_size:1 mux,
  // each element_width bits wide.
  //
  // Delay calibrated against real synthesis of a register file's read
  // port (benchmarking/fastppa_scaling/regfile_{4,8,16,32,64}.sv,
  // critical path isolated via `report_checks -from raddr` since the
  // write port can otherwise dominate at small array sizes): a pure
  // log2(array_size) logic-depth model gets the *level count* right
  // (real synthesis matches log2(array_size) almost exactly) but misses
  // that the address bits driving the decode fan out to ~array_size
  // places -- at array_size>=16, real synthesis inserts a buffering
  // inverter whose own delay (driven by that fan-out) dominates the
  // path, e.g. a 32-entry read measured 0.97 ns real critical path vs
  // the old model's 125 ps (~8x low).
  //
  // Area calibrated separately against benchmarking/fastppa_scaling/
  // idx_{4,8,16,32,64}.sv, which gives every entry an independent write
  // enable (no address-decoded write) so the measured area isolates the
  // read decode/mux tree without the write port's own decode logic
  // mixed in. Area is close to linear in array_size, not
  // log(array_size) (real decode/mux-tree gate count grows linearly
  // with the number of array elements).
  double n = static_cast<double>(element_width);
  double size = static_cast<double>(array_size > 1 ? array_size : 2);
  double levels = std::ceil(std::log2(size));
  operator_costt cost;
  cost.area_um2 = n * (2.82 * size + 5.12) * scale_area;
  cost.delay_ps = (27.1 * levels + 25.8 * size) * scale_delay;
  cost.energy_fj = n * (0.75 * size + 1.37) * scale_energy;
  return cost;
}
