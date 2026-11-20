/*******************************************************************\

Module: FastPPA operator cost tables

Author: Kiro

\*******************************************************************/

#include "cost_table.h"

#include <util/exit_codes.h>

#include <ebmc/ebmc_error.h>

#include <algorithm>
#include <cmath>
#include <fstream>
#include <sstream>

static const std::map<std::string, cost_formt> &form_names()
{
  static const std::map<std::string, cost_formt> names = {
    {"1", cost_formt::ONE},
    {"w", cost_formt::W},
    {"logw", cost_formt::LOGW},
    {"wlogw", cost_formt::WLOGW},
    {"w2", cost_formt::W2},
    {"n", cost_formt::N},
    {"logn", cost_formt::LOGN},
    {"wn", cost_formt::WN},
    {"wn1", cost_formt::WN1}};
  return names;
}

cost_formt cost_form_from_string(const std::string &s)
{
  auto it = form_names().find(s);
  if(it == form_names().end())
    throw ebmc_errort{} << "unknown cost form " << s;
  return it->second;
}

std::string to_string(cost_formt form)
{
  for(auto &[name, f] : form_names())
    if(f == form)
      return name;
  return "?";
}

double evaluate(cost_formt form, std::size_t w, std::size_t n)
{
  const double W = static_cast<double>(std::max<std::size_t>(w, 1));
  const double N = static_cast<double>(std::max<std::size_t>(n, 1));

  switch(form)
  {
  case cost_formt::ONE:
    return 1;
  case cost_formt::W:
    return W;
  case cost_formt::LOGW:
    return std::log2(W);
  case cost_formt::WLOGW:
    return W * std::log2(W);
  case cost_formt::W2:
    return W * W;
  case cost_formt::N:
    return N;
  case cost_formt::LOGN:
    return std::log2(N);
  case cost_formt::WN:
    return W * N;
  case cost_formt::WN1:
    return W * (N - 1);
  }

  return 0;
}

cost_tablet cost_tablet::from_stream(std::istream &in, const std::string &name)
{
  cost_tablet result;
  std::string line;
  std::size_t line_no = 0;

  while(std::getline(in, line))
  {
    ++line_no;
    if(line.empty() || line[0] == '#')
      continue;
    std::istringstream s{line};
    std::string kind, area_form, delay_form;
    cost_functiont f;
    if(!(s >> kind >> area_form >> f.a0 >> f.a1 >> delay_form >> f.d0 >> f.d1 >>
         f.e0 >> f.e1 >> f.l0 >> f.l1))
    {
      throw ebmc_errort{} << name << ':' << line_no
                          << ": malformed cost table entry";
    }
    f.area_form = cost_form_from_string(area_form);
    f.delay_form = cost_form_from_string(delay_form);
    result.table[kind] = f;
  }

  return result;
}

cost_tablet cost_tablet::from_file(const std::string &file_name)
{
  std::ifstream in{file_name};
  if(!in)
    throw ebmc_errort{} << "failed to open cost table " << file_name;
  return from_stream(in, file_name);
}

namespace
{
struct builtin_tablet
{
  const char *name;
  const char *description;
  const char *table;
};

// See benchmarking/fastppa_eval/PROCESS_NODES.md for the sources.
const builtin_tablet builtin_tables[] = {
  {
    "gf180",
    "GF180MCU 9-track 5V, typical (measured)",
#include "cost_table_gf180.inc"
  },
  {
    "sky130",
    "SkyWater sky130_fd_sc_hd, typical (measured)",
#include "cost_table_sky130hd.inc"
  },
  {
    "ihp-sg13g2",
    "IHP SG13G2 130nm, typical (measured)",
#include "cost_table_ihp_sg13g2.inc"
  },
  {
    "90nm",
    "derived from nangate45 with DeepScaleTool factors",
#include "cost_table_90nm.inc"
  },
  {
    "65nm",
    "derived from nangate45 with DeepScaleTool factors",
#include "cost_table_65nm.inc"
  },
  {
    "nangate45",
    "Nangate Open Cell Library (FreePDK45), typical (measured)",
#include "cost_table_nangate45.inc"
  },
  {
    "28nm",
    "derived from nangate45 with DeepScaleTool factors",
#include "cost_table_28nm.inc"
  },
  {
    "14nm",
    "derived from nangate45 with DeepScaleTool factors",
#include "cost_table_14nm.inc"
  },
  {
    "asap7",
    "ASAP7 predictive 7nm FinFET, RVT, typical (measured)",
#include "cost_table_asap7.inc"
  },
  {
    "5nm",
    "derived from asap7 with TSMC's N7 to N5 figures",
#include "cost_table_5nm.inc"
  },
  {
    "3nm",
    "derived from asap7 with TSMC's N7 to N3 figures",
#include "cost_table_3nm.inc"
  },
  {
    "gt2n",
    "GT2N predictive 2nm nanosheet, LVT, typical (measured)",
#include "cost_table_gt2n.inc"
  }};

// Node names for the measured tables.
const std::map<std::string, std::string> aliases = {
  {"180nm", "gf180"},
  {"130nm", "sky130"},
  {"45nm", "nangate45"},
  {"7nm", "asap7"},
  {"2nm", "gt2n"}};
} // namespace

const std::map<std::string, std::string> &cost_tablet::process_names()
{
  static const std::map<std::string, std::string> names = []
  {
    std::map<std::string, std::string> result;
    for(auto &t : builtin_tables)
      result[t.name] = t.description;
    for(auto &[alias, name] : aliases)
      result[alias] = "same as " + name;
    return result;
  }();
  return names;
}

cost_tablet cost_tablet::builtin(const std::string &process)
{
  auto alias = aliases.find(process);
  const std::string &name = alias == aliases.end() ? process : alias->second;

  for(auto &t : builtin_tables)
  {
    if(name == t.name)
    {
      std::istringstream in{t.table};
      return from_stream(in, name);
    }
  }

  throw ebmc_errort{}.with_exit_code(CPROVER_EXIT_USAGE_ERROR)
    << "unknown process node: " << process;
}

const cost_functiont &cost_tablet::operator()(const std::string &kind) const
{
  auto it = table.find(kind);
  if(it == table.end())
    throw ebmc_errort{} << "cost table has no entry for " << kind;
  return it->second;
}
