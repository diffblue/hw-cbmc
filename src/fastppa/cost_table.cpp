/*******************************************************************\

Module: FastPPA operator cost tables

Author: Kiro

\*******************************************************************/

#include "cost_table.h"

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
    if(!(s >> kind >> area_form >> f.a0 >> f.a1 >> delay_form >> f.d0 >> f.d1))
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

cost_tablet cost_tablet::builtin(const std::string &name)
{
  static const std::map<std::string, const char *> tables = {{
    "nangate45",
#include "cost_table_nangate45.inc"
  }};

  auto it = tables.find(name);
  if(it == tables.end())
    throw ebmc_errort{} << "no cost table for " << name;

  std::istringstream in{it->second};
  return from_stream(in, name);
}

const cost_functiont &cost_tablet::operator()(const std::string &kind) const
{
  auto it = table.find(kind);
  if(it == table.end())
    throw ebmc_errort{} << "cost table has no entry for " << kind;
  return it->second;
}
