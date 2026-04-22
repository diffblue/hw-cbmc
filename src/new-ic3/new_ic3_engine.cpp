/*******************************************************************\

Module: New IC3 Engine

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Word-level IC3/PDR engine using CBMC's decision procedures.
/// Uses unwind() to encode the transition relation into boolbvt,
/// then operates on bit-level literals for cubes and clauses.
/// Inspired by rIC3 (arXiv:2502.13605).

#include "new_ic3_engine.h"

#include <util/invariant.h>

#include <ebmc/ebmc_error.h>
#include <ebmc/liveness_to_safety.h>
#include <ebmc/report_results.h>
#include <solvers/flattening/boolbv.h>
#include <solvers/sat/cnf_clause_list.h>
#include <solvers/sat/satcheck.h>

#include <ic3/minisat/minisat/core/Solver.h>
#include <temporal-logic/ctl.h>
#include <temporal-logic/ltl.h>
#include <temporal-logic/temporal_logic.h>
#include <trans-word-level/instantiate_word_level.h>
#include <trans-word-level/unwind.h>
#include <verilog/sva_expr.h>

#include <algorithm>
#include <chrono>
#include <queue>
#include <unordered_set>

/// A cnf_clause_listt that can be instantiated (provides missing virtuals).
class recording_cnft : public cnf_clause_listt
{
public:
  explicit recording_cnft(message_handlert &mh) : cnf_clause_listt(mh) {}
  bool is_in_conflict(literalt) const override { return false; }
  void set_assignment(literalt, bool) override {}
};

/// A cube is a conjunction of literals (state variable bit assignments).
using cubet = bvt;

/// A clause is a disjunction of literals (the negation of a cube).
using clauset = bvt;

/// A frame clause with its activation literal in the transition solver.
struct activated_clauset
{
  clauset clause;
  literalt activation; // in trans solver
};

/// A frame is a set of clauses (for subsumption tracking).
struct framet
{
  std::vector<activated_clauset> clauses;
};

/// Negate a cube to get a clause and vice versa.
static clauset negate_cube(const cubet &cube)
{
  clauset clause;
  clause.reserve(cube.size());
  for(auto l : cube)
    clause.push_back(!l);
  return clause;
}

/// Check if clause a subsumes clause b (a ⊆ b as literal sets).
static bool subsumes(const clauset &a, const clauset &b)
{
  if(a.size() > b.size())
    return false;
  for(auto la : a)
  {
    bool found = false;
    for(auto lb : b)
    {
      if(la == lb)
      {
        found = true;
        break;
      }
    }
    if(!found)
      return false;
  }
  return true;
}

/// Add a clause to a frame, removing subsumed clauses.
static void add_clause_to_frame(framet &frame, const activated_clauset &ac)
{
  for(const auto &existing : frame.clauses)
    if(subsumes(existing.clause, ac.clause))
      return;
  auto it =
    std::remove_if(frame.clauses.begin(), frame.clauses.end(), [&](const auto &fc) {
      return subsumes(ac.clause, fc.clause);
    });
  frame.clauses.erase(it, frame.clauses.end());
  frame.clauses.push_back(ac);
}

/// A proof obligation: a cube that must be blocked at a given frame level.
struct proof_obligationt
{
  cubet cube;
  std::size_t level;

  bool operator>(const proof_obligationt &other) const
  {
    return level > other.level;
  }
};

/// The IC3 solver uses per-frame SAT solvers via CNF replay.
/// The transition relation is encoded once into a cnf_clause_listt,
/// then copy_to'd into each per-frame satcheck_no_simplifiert.
/// Frame clauses are added permanently — no activation literals needed.
class ic3_solvert
{
public:
  ic3_solvert(
    const transt &trans_expr,
    const std::vector<symbol_exprt> &state_variables,
    const std::vector<symbol_exprt> &inputs,
    const exprt &property_expr,
    const namespacet &ns,
    message_handlert &message_handler);

  std::optional<cubet> check_initial_state();
  std::optional<cubet> solve_relative(std::size_t level, const cubet &);
  bool is_relative_inductive(std::size_t level, const cubet &);
  std::optional<cubet> solve_relative_bad(std::size_t level);
  bool is_inductive(std::size_t level, const clauset &clause);
  cubet generalize(std::size_t level, cubet cube);
  bool init_intersects(const cubet &);

  void add_clause(std::size_t level, const clauset &clause);
  void ensure_frame(std::size_t level);

  cubet last_reduced;

private:
  struct latch_infot
  {
    literalt current, next, init;
  };

  std::vector<latch_infot> latches;
  std::size_t num_state_latches;
  std::unordered_map<unsigned, std::size_t> current_to_latch;

  // Base transition CNF (recorded once, replayed into per-frame solvers)
  std::unique_ptr<recording_cnft> base_cnf;

  // Initial state solver
  std::unique_ptr<propt> init_prop;
  std::unique_ptr<boolbvt> init_solver;

  // Persistent lifting solver using IC3's MiniSAT (has releaseVar)
  std::unique_ptr<IctMinisat::Solver> lift_minisat;

  // Input literals (in base CNF variable space)
  bvt input_lits;

  // Per-frame SAT solvers
  struct frame_solvert
  {
    std::unique_ptr<satcheck_no_simplifiert> solver;
  };
  std::vector<frame_solvert> frame_solvers;
  message_handlert &msg_handler;

  // Clauses at each level (for replay when creating new frame solvers)
  std::vector<std::vector<clauset>> level_clauses;

  /// Get the SAT solver for a frame level (create if needed).
  satcheck_no_simplifiert &get_solver(std::size_t level);

  literalt prop_current, prop_next, bad_next, bad_init;

  static constexpr std::size_t NO_TIMEFRAMES = 2;

  std::vector<float> lit_activity;

  literalt to_next(literalt l) const;
  literalt to_init(literalt l) const;

  cubet extract_state(propt &solver);
  cubet lift(propt &solver, const cubet &full_state, const cubet &target_cube);
};

// ============================================================
// ic3_solvert implementation
// ============================================================

ic3_solvert::ic3_solvert(
  const transt &trans_expr,
  const std::vector<symbol_exprt> &state_variables,
  const std::vector<symbol_exprt> &inputs,
  const exprt &property_expr,
  const namespacet &ns,
  message_handlert &message_handler)
  : msg_handler(message_handler)
{
  // Encode transition relation into cnf_clause_listt (records CNF)
  base_cnf = std::make_unique<recording_cnft>(message_handler);
  {
    boolbvt converter(ns, *base_cnf, message_handler);
    const exprt &op_invar = trans_expr.invar();
    const exprt &op_trans = trans_expr.trans();
    if(!op_invar.is_true())
    {
      converter.set_to_true(instantiate(op_invar, 0, NO_TIMEFRAMES));
      converter.set_to_true(instantiate(op_invar, 1, NO_TIMEFRAMES));
    }
    if(!op_trans.is_true())
      converter.set_to_true(instantiate(op_trans, 0, NO_TIMEFRAMES));

    // Collect latch literals (same variable numbering as base_cnf)
    for(const auto &sv : state_variables)
    {
      const bvt &cur = converter.convert_bv(timeframe_symbol(0, sv));
      const bvt &nxt = converter.convert_bv(timeframe_symbol(1, sv));
      for(std::size_t i = 0; i < cur.size(); i++)
      {
        current_to_latch[cur[i].var_no()] = latches.size();
        latches.push_back({cur[i], nxt[i], literalt{}});
      }
    }

    // Property literals
    const exprt &p = to_unary_expr(property_expr).op();
    prop_current = converter.convert(instantiate(p, 0, NO_TIMEFRAMES));
    prop_next = converter.convert(instantiate(p, 1, NO_TIMEFRAMES));
    bad_next = !prop_next;

    // Input literals
    for(const auto &inp : inputs)
    {
      const bvt &inp_bv = converter.convert_bv(timeframe_symbol(0, inp));
      for(auto l : inp_bv)
        input_lits.push_back(l);
    }
  }

  // Create initial state solver
  init_prop = std::make_unique<satcheck_no_simplifiert>(message_handler);
  init_solver = std::make_unique<boolbvt>(ns, *init_prop, message_handler);
  unwind(trans_expr, message_handler, *init_solver, 1, ns, true);

  // Create lifting solver using IC3's MiniSAT (has releaseVar)
  lift_minisat = std::make_unique<IctMinisat::Solver>();
  {
    // Ensure enough variables
    auto nv = base_cnf->no_variables();
    while(lift_minisat->nVars() < (int)nv)
      lift_minisat->newVar();
    // Replay base CNF
    for(const auto &clause : base_cnf->get_clauses())
    {
      IctMinisat::vec<IctMinisat::Lit> mc;
      for(auto l : clause)
      {
        if(l.is_true()) continue;
        if(l.is_false()) { mc.clear(); break; }
        mc.push(IctMinisat::mkLit(l.var_no(), l.sign()));
      }
      if(mc.size() > 0)
        lift_minisat->addClause(mc);
    }
  }

  // Collect init latch literals
  for(std::size_t i = 0; i < latches.size(); i++)
  {
    // Find the corresponding state variable symbol
    // Use the same timeframe_symbol(0, sv) expression
  }
  // Simpler: re-collect init literals by iterating state variables again
  {
    std::size_t idx = 0;
    for(const auto &sv : state_variables)
    {
      const bvt &init_bv = init_solver->convert_bv(timeframe_symbol(0, sv));
      for(std::size_t i = 0; i < init_bv.size(); i++)
        latches[idx++].init = init_bv[i];
    }
  }

  bad_init = init_solver->convert(
    instantiate(not_exprt{to_unary_expr(property_expr).op()}, 0, 1));

  num_state_latches = latches.size();
  lit_activity.resize(num_state_latches, 0.0f);
  if(current_to_latch.find(prop_current.var_no()) == current_to_latch.end())
  {
    current_to_latch[prop_current.var_no()] = latches.size();
    latches.push_back({prop_current, prop_next, literalt{}});
  }
}

literalt ic3_solvert::to_next(literalt l) const
{
  auto it = current_to_latch.find(l.var_no());
  PRECONDITION(it != current_to_latch.end());
  const auto &latch = latches[it->second];
  // l might be positive or negative relative to latch.current
  return latch.next ^ (l.sign() != latch.current.sign());
}

literalt ic3_solvert::to_init(literalt l) const
{
  auto it = current_to_latch.find(l.var_no());
  PRECONDITION(it != current_to_latch.end());
  const auto &latch = latches[it->second];
  return latch.init ^ (l.sign() != latch.current.sign());
}

cubet ic3_solvert::extract_state(propt &solver)
{
  cubet cube;
  cube.reserve(num_state_latches);
  for(std::size_t i = 0; i < num_state_latches; i++)
  {
    tvt val = solver.l_get(latches[i].current);
    if(val.is_true())
      cube.push_back(latches[i].current);
    else if(val.is_false())
      cube.push_back(!latches[i].current);
    // skip don't-care (unknown) bits — smaller cubes
  }
  return cube;
}

void ic3_solvert::ensure_frame(std::size_t level)
{
  while(level_clauses.size() <= level)
    level_clauses.emplace_back();
}

satcheck_no_simplifiert &ic3_solvert::get_solver(std::size_t level)
{
  while(frame_solvers.size() <= level)
    frame_solvers.emplace_back();
  auto &fs = frame_solvers[level];
  if(!fs.solver)
  {
    fs.solver = std::make_unique<satcheck_no_simplifiert>(msg_handler);
    base_cnf->copy_to(*fs.solver);
    for(std::size_t j = level; j < level_clauses.size(); j++)
      for(const auto &cl : level_clauses[j])
        fs.solver->lcnf(cl);
  }
  return *fs.solver;
}

void ic3_solvert::add_clause(std::size_t level, const clauset &clause)
{
  ensure_frame(level);
  level_clauses[level].push_back(clause);
  // Add to existing frame solvers at levels <= level
  for(std::size_t i = 0; i <= level && i < frame_solvers.size(); i++)
    if(frame_solvers[i].solver)
      frame_solvers[i].solver->lcnf(clause);
}

std::optional<cubet> ic3_solvert::check_initial_state()
{
  bvt assumptions = {bad_init};
  if(init_prop->prop_solve(assumptions) == propt::resultt::P_SATISFIABLE)
  {
    cubet state;
    state.reserve(num_state_latches);
    for(std::size_t i = 0; i < num_state_latches; i++)
    {
      tvt val = init_prop->l_get(latches[i].init);
      if(val.is_true())
        state.push_back(latches[i].current);
      else
        state.push_back(!latches[i].current);
    }
    return state;
  }
  return std::nullopt;
}

bool ic3_solvert::init_intersects(const cubet &cube)
{
  bvt assumptions;
  assumptions.reserve(cube.size());
  for(auto l : cube)
    assumptions.push_back(to_init(l));
  return init_prop->prop_solve(assumptions) == propt::resultt::P_SATISFIABLE;
}

cubet ic3_solvert::lift(
  propt &query_solver,
  const cubet &full_state,
  const cubet &target_cube)
{
  auto &S = *lift_minisat;
  using namespace IctMinisat;

  // Activation literal for this query
  Var act_var = S.newVar();
  Lit act = mkLit(act_var, false);

  // Inputs as activated binary clauses: act → input_value
  for(auto l : input_lits)
  {
    tvt val = query_solver.l_get(l);
    if(!val.is_unknown())
    {
      Lit ml = mkLit(l.var_no(), val.is_false());
      S.addClause(~act, ml);
    }
  }

  // Negated target: act → (¬l1' ∨ ¬l2' ∨ ...)
  {
    vec<Lit> clause;
    clause.push(~act);
    for(auto l : target_cube)
    {
      auto nl = to_next(l);
      clause.push(mkLit(nl.var_no(), !nl.sign()));
    }
    S.addClause(clause);
  }

  // Solve with act + state as assumptions
  vec<Lit> assumptions;
  assumptions.push(act);
  for(auto l : full_state)
    assumptions.push(mkLit(l.var_no(), l.sign()));

  cubet result;
  if(!S.solve(assumptions))
  {
    // UNSAT — extract minimal state from conflict
    for(auto l : full_state)
    {
      Lit ml = mkLit(l.var_no(), l.sign());
      if(S.conflict.has(~ml))
        result.push_back(l);
    }
  }

  // Release activation literal (permanently set ~act, freeing the variable)
  S.releaseVar(~act);

  return result.empty() ? full_state : result;
}

bool ic3_solvert::is_relative_inductive(
  std::size_t level,
  const cubet &cube)
{
  auto &solver = get_solver(level);
  bvt assumptions;
  assumptions.reserve(cube.size());
  for(auto l : cube)
    assumptions.push_back(to_next(l));
  return solver.prop_solve(assumptions) != propt::resultt::P_SATISFIABLE;
}

std::optional<cubet>
ic3_solvert::solve_relative(std::size_t level, const cubet &cube)
{
  auto &solver = get_solver(level);
  bvt assumptions;
  assumptions.reserve(cube.size());
  for(auto l : cube)
    assumptions.push_back(to_next(l));

  if(solver.prop_solve(assumptions) == propt::resultt::P_SATISFIABLE)
    return lift(solver, extract_state(solver), cube);

  // UNSAT — cube is relatively inductive. Reduce using conflict.
  last_reduced.clear();
  for(auto l : cube)
    if(solver.is_in_conflict(to_next(l)))
      last_reduced.push_back(l);
  if(last_reduced.empty())
    last_reduced = cube;

  return std::nullopt;
}

std::optional<cubet>
ic3_solvert::solve_relative_bad(std::size_t level)
{
  auto &solver = get_solver(level);
  bvt assumptions = {bad_next};

  if(solver.prop_solve(assumptions) == propt::resultt::P_SATISFIABLE)
    return lift(solver, extract_state(solver), {!prop_current});

  return std::nullopt;
}

bool ic3_solvert::is_inductive(
  std::size_t level,
  const clauset &clause)
{
  auto &solver = get_solver(level);
  // Temporary activation for clause at timeframe 0
  literalt act = solver.new_variable();
  {
    bvt cnf;
    cnf.reserve(clause.size() + 1);
    cnf.push_back(!act);
    for(auto l : clause)
      cnf.push_back(l);
    solver.lcnf(cnf);
  }

  bvt assumptions;
  assumptions.reserve(clause.size() + 1);
  assumptions.push_back(act);
  for(auto l : clause)
    assumptions.push_back(!to_next(l));

  return solver.prop_solve(assumptions) == propt::resultt::P_UNSATISFIABLE;
}

cubet ic3_solvert::generalize(
  std::size_t level,
  cubet cube)
{
  // Use the conflict-reduced cube, adding back literals from the
  // original cube as needed to avoid intersecting init states.
  if(!last_reduced.empty() && last_reduced.size() < cube.size())
  {
    cubet candidate = last_reduced;
    if(init_intersects(candidate))
    {
      // Add back literals from cube that aren't in last_reduced
      for(auto l : cube)
      {
        bool in_reduced = false;
        for(auto rl : last_reduced)
          if(l == rl) { in_reduced = true; break; }
        if(!in_reduced)
        {
          candidate.push_back(l);
          if(!init_intersects(candidate))
            break; // enough to avoid init
        }
      }
    }
    if(!init_intersects(candidate))
      cube = candidate;
  }

  // Ensure it doesn't intersect init
  if(init_intersects(cube))
    return cube;

  // Sort by activity: drop least-active literals first
  std::sort(cube.begin(), cube.end(), [&](literalt a, literalt b) {
    auto ia = current_to_latch.find(a.var_no());
    auto ib = current_to_latch.find(b.var_no());
    float aa = (ia != current_to_latch.end() && ia->second < num_state_latches)
                 ? lit_activity[ia->second] : 0.0f;
    float ab = (ib != current_to_latch.end() && ib->second < num_state_latches)
                 ? lit_activity[ib->second] : 0.0f;
    return aa < ab;
  });

  // CTG parameters (matching rIC3 defaults)
  static constexpr std::size_t CTG_MAX = 3;

  // ctg_down: check if cand is relatively inductive, with CTG support.
  // Uses cheap is_relative_inductive (no lifting).
  auto ctg_down = [&](cubet &cand) -> bool {
    std::size_t num_ctg = 0;
    // cand is a subset of cube which doesn't intersect init,
    // so cand also doesn't intersect init initially.
    bool init_safe = true;
    while(true)
    {
      if(!init_safe && init_intersects(cand))
        return false;
      init_safe = false;

      // Check relative inductiveness (1 SAT call, no lifting)
      auto &solver = get_solver(level);
      bvt assumptions;
      assumptions.reserve(cand.size());
      for(auto l : cand)
        assumptions.push_back(to_next(l));

      if(solver.prop_solve(assumptions) != propt::resultt::P_SATISFIABLE)
        return true; // relatively inductive

      // Extract predecessor from model (no lifting — just for intersection)
      cubet p = extract_state(solver);

      // CTG: try to block predecessor
      if(num_ctg < CTG_MAX && level > 0 && !init_intersects(p) &&
         is_relative_inductive(level, p))
      {
        clauset blocking = negate_cube(p);
        add_clause(level, blocking);
        num_ctg++;
        continue;
      }

      // Intersect cand with predecessor
      num_ctg = 0;
      cubet intersection;
      for(auto l : cand)
        for(auto pl : p)
          if(l == pl)
          {
            intersection.push_back(l);
            break;
          }
      if(intersection.empty() || intersection.size() >= cand.size())
        return false;
      cand = intersection;
      init_safe = true; // subset of previous cand
    }
  };

  // Compositional shortening: start from a small subset, iteratively
  // add literals from the UNSAT conflict until reaching a fixed point.
  // This finds a small inductive sub-cube in 2-3 SAT calls.
  if(cube.size() > 10)
  {
    // Start with the least-active literal (first after sorting)
    cubet candidate = {cube[0]};

    for(std::size_t iter = 0; iter < cube.size(); iter++)
    {
      if(init_intersects(candidate))
        break;

      auto &solver = get_solver(level);
      bvt assumptions;
      assumptions.reserve(candidate.size());
      for(auto l : candidate)
        assumptions.push_back(to_next(l));

      if(solver.prop_solve(assumptions) != propt::resultt::P_SATISFIABLE)
      {
        // Found an inductive sub-cube! Use conflict to tighten.
        cubet reduced;
        for(auto l : candidate)
          if(solver.is_in_conflict(to_next(l)))
            reduced.push_back(l);
        if(!reduced.empty() && !init_intersects(reduced))
          candidate = reduced;
        cube = candidate;
        break;
      }

      // Not inductive — add literals from full cube that match predecessor
      cubet p = extract_state(solver);
      std::size_t old_size = candidate.size();
      for(auto l : cube)
      {
        bool in_candidate = false;
        for(auto cl : candidate)
          if(l == cl) { in_candidate = true; break; }
        if(in_candidate)
          continue;
        for(auto pl : p)
          if(l == pl)
          {
            candidate.push_back(l);
            break;
          }
      }

      if(candidate.size() == old_size || candidate.size() >= cube.size())
        break; // no progress
    }
  }

  // Fine-grained: try dropping each remaining literal
  std::size_t i = 0;
  while(i < cube.size() && cube.size() > 1)
  {
    cubet cand;
    cand.reserve(cube.size() - 1);
    for(std::size_t j = 0; j < cube.size(); j++)
    {
      if(j != i)
        cand.push_back(cube[j]);
    }

    if(ctg_down(cand))
      cube = cand;
    else
      i++;
  }
  // Bump activity for literals that survived generalization
  for(auto l : cube)
  {
    auto it = current_to_latch.find(l.var_no());
    if(it != current_to_latch.end() && it->second < num_state_latches)
      lit_activity[it->second] += 1.0f;
  }

  return cube;
}

// ============================================================
// Main IC3 algorithm
// ============================================================

static bool new_ic3_supports_property(const exprt &expr)
{
  if(!is_temporal_operator(expr))
    return false;
  if(expr.id() == ID_sva_always)
    return !has_temporal_operator(to_sva_always_expr(expr).op());
  if(expr.id() == ID_G)
    return !has_temporal_operator(to_G_expr(expr).op());
  if(expr.id() == ID_AG)
    return !has_temporal_operator(to_AG_expr(expr).op());
  return false;
}

enum class ic3_resultt
{
  PROVED,
  REFUTED
};

static ic3_resultt ic3_check_property(
  const exprt &property_expr,
  const transt &trans_expr,
  const std::vector<symbol_exprt> &state_variables,
  const std::vector<symbol_exprt> &inputs,
  const namespacet &ns,
  message_handlert &message_handler)
{
  messaget message{message_handler};

  ic3_solvert solver(
    trans_expr, state_variables, inputs, property_expr, ns, message_handler);

  auto start_time = std::chrono::steady_clock::now();

  // Check: can initial states violate the property?
  if(solver.check_initial_state().has_value())
  {
    message.result() << "Property violated in initial state" << messaget::eom;
    return ic3_resultt::REFUTED;
  }

  // Frames for subsumption tracking only
  std::vector<framet> frames;
  frames.emplace_back(); // F_0
  solver.ensure_frame(0);

  while(true)
  {
    std::size_t k = frames.size();
    frames.emplace_back();
    solver.ensure_frame(k);

    message.progress() << "IC3: frame " << k << messaget::eom;

    std::priority_queue<
      proof_obligationt,
      std::vector<proof_obligationt>,
      std::greater<proof_obligationt>>
      obligations;

    // Blocking phase
    // Track blocked cubes to skip duplicate obligations
    std::unordered_set<std::size_t> blocked_hashes;
    auto cube_hash = [](const cubet &c) {
      std::size_t h = c.size();
      for(auto l : c)
        h ^= std::hash<unsigned>{}(l.get()) + 0x9e3779b9 + (h << 6) + (h >> 2);
      return h;
    };

    while(true)
    {
      auto predecessor = solver.solve_relative_bad(k - 1);
      if(!predecessor.has_value())
        break;

      obligations.push({predecessor.value(), k - 1});

      while(!obligations.empty())
      {
      auto [cube, level] = obligations.top();
      obligations.pop();

      // Skip if this cube was already blocked
      auto h = cube_hash(cube);
      if(blocked_hashes.count(h))
        continue;

      if(level == 0)
      {
        if(solver.init_intersects(cube))
        {
          message.result() << "Property refuted" << messaget::eom;
          return ic3_resultt::REFUTED;
        }
        else
        {
          clauset blocking = negate_cube(cube);
          add_clause_to_frame(frames[0], {blocking, literalt{}});
          solver.add_clause(0, blocking);
          continue;
        }
      }

      auto pred = solver.solve_relative(level - 1, cube);
      if(pred.has_value())
      {
        obligations.push({pred.value(), level - 1});
        obligations.push({cube, level});
      }
      else
      {
        cubet generalized = solver.generalize(level - 1, cube);
        clauset blocking = negate_cube(generalized);
        activated_clauset ac = {blocking, literalt{}};

        for(std::size_t i = 1; i <= level; i++)
        {
          add_clause_to_frame(frames[i], ac);
          solver.add_clause(i, blocking);
        }
        blocked_hashes.insert(cube_hash(cube));

        // Re-queue at level+1 to push the blocking clause higher
        if(level + 1 < k)
          obligations.push({cube, level + 1});
      }
      }
    } // end blocking phase

    // Propagation: push clauses from F_i to F_{i+1}
    for(std::size_t i = 1; i < k; i++)
    {
      framet &fi = frames[i];
      framet &fi1 = frames[i + 1];
      bool all_pushed = true;

      for(const auto &ac : fi.clauses)
      {
        // Skip if already in F_{i+1}
        bool already_pushed = false;
        for(const auto &fc : fi1.clauses)
          if(fc.clause == ac.clause)
          {
            already_pushed = true;
            break;
          }

        if(already_pushed || solver.is_inductive(i, ac.clause))
        {
          add_clause_to_frame(fi1, ac);
          solver.add_clause(i + 1, ac.clause);
        }
        else
          all_pushed = false;
      }

      if(all_pushed && !fi.clauses.empty())
      {
        auto end_time = std::chrono::steady_clock::now();
        message.statistics()
          << "IC3: converged at frame " << i << " in "
          << std::chrono::duration<double>(end_time - start_time).count()
          << " seconds" << messaget::eom;
        return ic3_resultt::PROVED;
      }
    }
  }
}

property_checker_resultt new_ic3_engine(
  const cmdlinet &cmdline,
  transition_systemt &transition_system,
  ebmc_propertiest &properties,
  message_handlert &message_handler)
{
  messaget message{message_handler};

  if(!properties.has_unfinished_property())
    return property_checker_resultt{properties};

  if(cmdline.isset("liveness-to-safety"))
    liveness_to_safety(transition_system, properties);

  for(auto &property : properties.properties)
  {
    if(property.is_assumed())
    {
      message.error() << "no support for assumptions" << messaget::eom;
      return property_checker_resultt::error();
    }
  }

  const namespacet ns(transition_system.symbol_table);
  const auto state_variables = transition_system.state_variables();
  const auto inputs = transition_system.inputs();

  message.statistics() << "State variables: " << state_variables.size()
                       << messaget::eom;

  for(auto &property : properties.properties)
  {
    if(property.is_disabled())
      continue;

    if(!new_ic3_supports_property(property.normalized_expr))
    {
      property.failure("property not supported by new IC3 engine");
      continue;
    }

    message.status() << "Checking " << property.name << " with new IC3 engine"
                     << messaget::eom;

    auto result = ic3_check_property(
      property.normalized_expr,
      transition_system.trans_expr,
      state_variables,
      inputs,
      ns,
      message_handler);

    switch(result)
    {
    case ic3_resultt::PROVED:
      property.proved();
      break;
    case ic3_resultt::REFUTED:
      property.refuted();
      break;
    }
  }

  return property_checker_resultt{properties};
}
