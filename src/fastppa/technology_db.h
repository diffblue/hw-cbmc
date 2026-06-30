/*******************************************************************\

Module: Technology Database for FastPPA Estimation

Author: Kiro

\*******************************************************************/

#ifndef CPROVER_FASTPPA_TECHNOLOGY_DB_H
#define CPROVER_FASTPPA_TECHNOLOGY_DB_H

#include <util/irep.h>

#include <cmath>
#include <string>
#include <unordered_map>

struct operator_costt
{
  double area_um2 = 0;
  double delay_ps = 0;
  double energy_fj = 0;
};

/// Technology characterization: maps operator ID + bit-width to cost.
class technology_dbt
{
public:
  explicit technology_dbt(const std::string &process_name);

  operator_costt operator_cost(const irep_idt &op, std::size_t width) const;
  operator_costt
  constant_mult_cost(std::size_t width, std::size_t constant_bits) const;
  operator_costt
  index_cost(std::size_t element_width, std::size_t array_size) const;
  operator_costt register_cost(std::size_t width) const;
  operator_costt mux_cost(std::size_t width, std::size_t inputs) const;

  const std::string &name() const
  {
    return process;
  }
  double leakage_scale() const
  {
    return scale_leakage;
  }
  double area_scale() const
  {
    return scale_area;
  }
  double energy_scale() const
  {
    return scale_energy;
  }
  double wire_delay_fraction() const
  {
    return wire_delay_cap;
  }

private:
  std::string process;

  // Base costs per bit at the reference node, scaled per process
  double scale_area;     // relative to 45nm
  double scale_delay;    // relative to 45nm
  double scale_energy;   // relative to 45nm
  double scale_leakage;  // leakage power scaling
  double wire_delay_cap; // max wire delay as fraction of comb delay
};

#endif // CPROVER_FASTPPA_TECHNOLOGY_DB_H
