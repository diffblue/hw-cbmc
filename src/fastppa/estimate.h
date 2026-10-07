/*******************************************************************\

Module: FastPPA Estimation Engine

Author: Kiro

\*******************************************************************/

#ifndef CPROVER_FASTPPA_ESTIMATE_H
#define CPROVER_FASTPPA_ESTIMATE_H

#include <util/expr.h>
#include <util/mathematical_expr.h>

#include <trans-word-level/word_level_trans.h>

#include "technology_db.h"

struct node_costt
{
  double arrival_ps = 0;
  double area_um2 = 0;
  double energy_fj = 0;
  std::size_t depth = 0;

  // Bookkeeping for associative-chain delay balancing (see walk_expr):
  // real synthesis restructures literal left/right-associative chains of
  // +, &, |, ^ (e.g. a sum-of-products written as ((a+b)+c)+d) into a
  // balanced tree, so a chain of N terms costs ~log2(N) stages, not N.
  // chain_length counts the terms merged so far; chain_leaf_max_ps is the
  // slowest leaf feeding the chain, i.e. what the balanced tree's delay
  // gets added on top of.
  std::size_t chain_length = 1;
  double chain_leaf_max_ps = 0;
};

struct estimation_resultt
{
  double total_area_um2 = 0;
  double register_area_um2 = 0;
  double combinational_area_um2 = 0;
  double critical_path_ps = 0;
  double total_energy_fj = 0;
  double activity_ratio = 1.0; // fraction of logic active per cycle (from RTL)
  std::size_t register_bits = 0;
  std::size_t combinational_depth = 0;
  std::size_t operator_count = 0;
};

estimation_resultt estimate(
  const word_level_transt &wl_trans,
  const transt &trans_expr,
  const std::vector<symbol_exprt> &state_vars,
  const technology_dbt &tech);

#endif // CPROVER_FASTPPA_ESTIMATE_H
