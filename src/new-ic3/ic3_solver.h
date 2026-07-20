/*******************************************************************\

Module: IC3 Solver

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Per-frame SAT solver infrastructure for IC3/PDR, operating on
/// the netlist (AIG) encoding of the transition system.

#ifndef CPROVER_NEW_IC3_IC3_SOLVER_H
#define CPROVER_NEW_IC3_IC3_SOLVER_H

#include <solvers/prop/literal.h>
#include <solvers/sat/satcheck.h>
#include <trans-netlist/netlist.h>

#include <memory>
#include <optional>
#include <unordered_map>
#include <vector>

/// A cube is a conjunction of literals (state variable bit assignments).
using cubet = bvt;

/// A clause is a disjunction of literals (the negation of a cube).
using clauset = bvt;

/// Negate a cube to get a clause and vice versa.
clauset negate_cube(const cubet &cube);

class cnft;
class recording_cnft;

namespace IctMinisat
{
class Solver;
}

struct ic3_resultt
{
  enum class outcomet
  {
    PROVED,
    REFUTED
  } outcome;

  /// When REFUTED, the number of states in the counterexample trace:
  /// the trace has states at timeframes 0, ..., length - 1, and the
  /// property-violating state is at timeframe length - 1.
  /// The trace is genuine, but not guaranteed to be a shortest
  /// counterexample: obligations are processed by frame level, not by
  /// depth, so a longer chain of predecessors may reach an initial
  /// state before a minimal-length one is explored.
  std::size_t counterexample_length = 0;

  static ic3_resultt proved()
  {
    return {outcomet::PROVED, 0};
  }

  static ic3_resultt refuted(std::size_t counterexample_length)
  {
    return {outcomet::REFUTED, counterexample_length};
  }
};

/// The IC3 solver uses per-frame SAT solvers via CNF replay.
/// The netlist is encoded once into a cnf_clause_listt, then replayed
/// into each per-frame solver. The per-frame solvers use IC3's MiniSAT,
/// whose releaseVar allows disposable activation literals without
/// unbounded solver growth, and keep their learnt clauses for the
/// whole run.
///
/// Frames are kept as deltas: a clause stored at level j holds in
/// F_i for all i <= j, and the solver for level i contains the
/// clauses of all levels >= i. F_0 additionally contains the initial
/// state constraint.
class ic3_solvert
{
public:
  ic3_solvert(
    const netlistt &,
    literalt property_literal,
    message_handlert &message_handler);

  ~ic3_solvert();

  /// Run the IC3 algorithm. Returns PROVED or REFUTED; when refuted,
  /// the result includes the length of the counterexample trace.
  ic3_resultt solve();

private:
  message_handlert &message_handler;

  struct frame_clauset;

  static bool subsumes(const frame_clauset &a, const frame_clauset &b);

  bool initial_state_is_bad();
  std::optional<cubet> solve_relative(std::size_t level, const cubet &);
  std::optional<cubet> solve_bad(std::size_t level);
  cubet generalize(std::size_t level, cubet cube);
  bool init_intersects(const cubet &);
  bool is_blocked(const cubet &, std::size_t level);
  void add_clause(std::size_t level, const clauset &clause);
  void new_frame();
  std::size_t number_of_frames() const;
  bool propagate();

  cubet core;

  std::size_t num_queries = 0, num_lifts = 0, num_clauses_added = 0;
  std::size_t total_clauses() const;
  double average_clause_size() const;

  struct latch_infot
  {
    literalt current, next;
  };

  std::vector<latch_infot> latches;
  std::unordered_map<unsigned, std::size_t> current_to_latch;

  null_message_handlert solver_message_handler;

  std::unique_ptr<recording_cnft> base_cnf;
  bvt init_units;

  void replay_base_cnf(cnft &dest, bool with_init);

  std::unique_ptr<satcheck_no_simplifiert> init_solver;

  std::vector<tvt> init_values;
  bool init_is_unique_state = false;

  std::unique_ptr<IctMinisat::Solver> lift_minisat;

  bvt input_lits;

  std::vector<std::unique_ptr<IctMinisat::Solver>> frame_solvers;

  std::vector<std::vector<frame_clauset>> frame_clauses;

  std::unique_ptr<IctMinisat::Solver> new_minisat_solver();

  IctMinisat::Solver &get_solver(std::size_t level);

  literalt prop_current;

  // Max CTG (counterexample-to-generalization) attempts per generalize call.
  std::size_t ctg_max = 3;
  // Max join steps (intersection with predecessor) before giving up
  static constexpr std::size_t JOIN_MAX = 3;
  // Max consecutive MIC literal-drop failures before early termination
  static constexpr std::size_t MIC_FAIL_MAX = 2;

  static constexpr bool WITH_NEGATED_CUBE = true;

  std::vector<float> lit_activity;

  literalt to_next(literalt l) const;

  cubet extract_state(const IctMinisat::Solver &);

  cubet lift(
    const IctMinisat::Solver &query_solver,
    const cubet &full_state,
    const bvt &target_clause);

  bool relative_induction(
    std::size_t level,
    const cubet &cube,
    cubet *predecessor,
    bool lift_predecessor);

  void repair_init(const cubet &cube, cubet &reduced);

  bool ctg_down(std::size_t level, cubet &cand, std::size_t &ctg_budget);
};

#endif // CPROVER_NEW_IC3_IC3_SOLVER_H
