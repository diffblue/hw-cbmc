/*******************************************************************\

Module: Benchmark for early variable quantification in BDD model checking

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Compares monolithic vs early-quantification EX image computation.
///
/// Metric: peak BDD node count of the intermediate result, measured
/// after each conjunction and quantification step. This directly
/// reflects memory usage — the primary bottleneck in BDD-based
/// model checking. It is deterministic and reproducible. Wall-clock
/// time is reported as a secondary metric.
///
/// The benchmark uses N independent register bits (s_i' == s_i)
/// where the BDD variable ordering places all current-state
/// variables before all next-state variables. With this separated
/// ordering, the monolithic conjunction of all transition conjuncts
/// creates a BDD that grows as O(3^N). Early quantification
/// eliminates each next-state variable immediately after its
/// conjunct, keeping the intermediate BDD constant-size.

#include <ebmc/bdd_model_checker.h>

#include <chrono>
#include <cstdlib>
#include <iostream>
#include <set>

/// Count the number of nodes in a single BDD.
static std::size_t
bdd_node_count(const mini_bddt &bdd, std::set<unsigned> &visited)
{
  if(bdd.is_constant())
    return 0;
  if(!visited.insert(bdd.node_number()).second)
    return 0;
  return 1 + bdd_node_count(bdd.low(), visited) +
         bdd_node_count(bdd.high(), visited);
}

static std::size_t bdd_node_count(const mini_bddt &bdd)
{
  std::set<unsigned> visited;
  return bdd_node_count(bdd, visited);
}

static void bdd_support(const mini_bddt &bdd, std::set<unsigned> &vars)
{
  if(bdd.is_constant())
    return;
  if(!vars.insert(bdd.var()).second)
    return;
  bdd_support(bdd.low(), vars);
  bdd_support(bdd.high(), vars);
}

/// Build N register bits with separated variable ordering.
/// Variables ordered: s0, s1, ..., s_{N-1}, s0', s1', ..., s_{N-1}'.
/// Transition conjunct i: s_i' == s_i.
///
/// With this ordering, the monolithic conjunction
///   (s0' == s0) & (s1' == s1) & ... & (s_{N-1}' == s_{N-1})
/// grows as O(3^N) because each s_i' is far from s_i in the
/// variable ordering, preventing BDD sharing.
///
/// Early quantification eliminates each s_i' right after conjunct i
/// (no later conjunct mentions s_i'), collapsing the intermediate
/// BDD back to constant size.
static bdd_transition_relationt
make_identity(mini_bdd_mgrt &mgr, unsigned n_bits)
{
  bdd_transition_relationt tr;

  // All current-state variables first.
  std::vector<mini_bddt> current(n_bits);
  for(unsigned i = 0; i < n_bits; i++)
    current[i] = mgr.Var("s" + std::to_string(i));

  // All next-state variables after.
  std::vector<mini_bddt> next(n_bits);
  for(unsigned i = 0; i < n_bits; i++)
    next[i] = mgr.Var("s" + std::to_string(i) + "'");

  for(unsigned i = 0; i < n_bits; i++)
  {
    tr.variables.push_back({current[i], next[i]});
    tr.transition_conjuncts.push_back(next[i] == current[i]);
  }

  return tr;
}

/// Monolithic EX: conjoin all, then quantify. Track peak BDD size.
static void monolithic_EX(
  const bdd_transition_relationt &tr,
  const mini_bddt &property_next,
  std::size_t &peak_nodes,
  double &seconds)
{
  auto start = std::chrono::steady_clock::now();

  mini_bddt conjunction = property_next;
  peak_nodes = bdd_node_count(conjunction);

  for(const auto &t : tr.transition_conjuncts)
  {
    conjunction = conjunction & t;
    auto n = bdd_node_count(conjunction);
    if(n > peak_nodes)
      peak_nodes = n;
  }

  mini_bddt result = conjunction;
  conjunction.clear();

  for(const auto &v : tr.variables)
  {
    result = exists(result, v.next.var());
    auto n = bdd_node_count(result);
    if(n > peak_nodes)
      peak_nodes = n;
  }

  auto end = std::chrono::steady_clock::now();
  seconds = std::chrono::duration<double>(end - start).count();
}

/// Early-quantification EX: interleave conjunction and quantification.
/// Track peak BDD size.
static void early_EX(
  const bdd_transition_relationt &tr,
  const mini_bddt &property_next,
  std::size_t &peak_nodes,
  double &seconds)
{
  auto start = std::chrono::steady_clock::now();

  const auto &conjuncts = tr.transition_conjuncts;

  std::set<unsigned> next_vars;
  for(const auto &v : tr.variables)
    next_vars.insert(v.next.var());

  std::vector<std::set<unsigned>> supports(conjuncts.size());
  for(std::size_t i = 0; i < conjuncts.size(); i++)
    bdd_support(conjuncts[i], supports[i]);

  mini_bddt result = property_next;
  peak_nodes = bdd_node_count(result);

  for(std::size_t i = 0; i < conjuncts.size(); i++)
  {
    result = result & conjuncts[i];
    auto n = bdd_node_count(result);
    if(n > peak_nodes)
      peak_nodes = n;

    std::set<unsigned> remaining;
    for(auto var : next_vars)
    {
      bool needed = false;
      for(std::size_t j = i + 1; j < conjuncts.size(); j++)
      {
        if(supports[j].count(var))
        {
          needed = true;
          break;
        }
      }
      if(needed)
        remaining.insert(var);
      else
      {
        result = exists(result, var);
        n = bdd_node_count(result);
        if(n > peak_nodes)
          peak_nodes = n;
      }
    }
    next_vars = std::move(remaining);
  }

  auto end = std::chrono::steady_clock::now();
  seconds = std::chrono::duration<double>(end - start).count();
}

int main(int argc, char *argv[])
{
  unsigned max_bits = 16;
  if(argc > 1)
    max_bits = std::atoi(argv[1]);

  std::cout
    << "# Identity relation (s_i' == s_i) with separated variable ordering\n"
    << "# Monolithic peak nodes grow as O(3^N); early quantification "
       "stays O(1).\n";
  std::cout
    << "bits,monolithic_peak_nodes,early_peak_nodes,monolithic_sec,early_sec\n";

  for(unsigned n = 2; n <= max_bits; n++)
  {
    mini_bdd_mgrt mgr_mono;
    auto tr_mono = make_identity(mgr_mono, n);

    std::size_t mono_peak;
    double mono_sec;
    monolithic_EX(tr_mono, mgr_mono.True(), mono_peak, mono_sec);

    mini_bdd_mgrt mgr_early;
    auto tr_early = make_identity(mgr_early, n);

    std::size_t early_peak;
    double early_sec;
    early_EX(tr_early, mgr_early.True(), early_peak, early_sec);

    std::cout << n << "," << mono_peak << "," << early_peak << "," << mono_sec
              << "," << early_sec << "\n";
  }

  return 0;
}
