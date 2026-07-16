/*******************************************************************\

Module: IC3 Solver

Author: Daniel Kroening, dkr@amazon.com

\*******************************************************************/

/// \file
/// Per-frame SAT solver infrastructure for IC3/PDR, operating on
/// the netlist (AIG) encoding of the transition system.

#include "ic3_solver.h"

#include <util/invariant.h>

#include <ic3/minisat/minisat/core/Solver.h>
#include <solvers/sat/cnf_clause_list.h>
#include <solvers/sat/satcheck.h>
#include <trans-netlist/bmc_map.h>
#include <trans-netlist/unwind_netlist.h>

#include <algorithm>
#include <chrono>
#include <queue>
#include <unordered_set>

/// A cnf_clause_listt that can be instantiated (provides missing virtuals).
class recording_cnft : public cnf_clause_listt
{
public:
  explicit recording_cnft(message_handlert &mh) : cnf_clause_listt(mh)
  {
  }
  bool is_in_conflict(literalt) const override
  {
    return false;
  }
  void set_assignment(literalt, bool) override
  {
  }
};

/// A frame clause: literals sorted by literal code, plus a Bloom-style
/// signature for constant-time subsumption rejection.
struct ic3_solvert::frame_clauset
{
  clauset clause; // sorted by literalt::get()
  // Bloom signature: each literal sets bit (lit_code & 63). 64 bits
  // matches the register width on x86-64, giving a single-instruction
  // shift and a cheap early-reject in subsumes().
  uint64_t sig;

  explicit frame_clauset(clauset c) : clause(std::move(c))
  {
    std::sort(
      clause.begin(),
      clause.end(),
      [](literalt a, literalt b) { return a.get() < b.get(); });
    sig = 0;
    for(auto l : clause)
      sig |= uint64_t(1) << (l.get() & 63);
  }

  bool operator==(const frame_clauset &other) const
  {
    return clause == other.clause;
  }
};

clauset negate_cube(const cubet &cube)
{
  clauset clause;
  clause.reserve(cube.size());
  for(auto l : cube)
    clause.push_back(!l);
  return clause;
}

/// Check if clause a subsumes clause b (a ⊆ b as literal sets).
/// Both literal vectors must be sorted by literal code.
bool ic3_solvert::subsumes(
  const ic3_solvert::frame_clauset &a,
  const ic3_solvert::frame_clauset &b)
{
  if(a.clause.size() > b.clause.size())
    return false;
  if((a.sig & ~b.sig) != 0)
    return false;
  return std::includes(
    b.clause.begin(),
    b.clause.end(),
    a.clause.begin(),
    a.clause.end(),
    [](literalt x, literalt y) { return x.get() < y.get(); });
}

/// Translate a (non-constant) CBMC literal to an IC3-MiniSAT literal.
static inline IctMinisat::Lit to_minisat(literalt l)
{
  return IctMinisat::mkLit(l.var_no(), l.sign());
}

/// Add a clause of CBMC literals to an IC3-MiniSAT solver.
/// Tautologies are skipped; false literals are dropped.
static void add_minisat_clause(IctMinisat::Solver &S, const bvt &clause)
{
  IctMinisat::vec<IctMinisat::Lit> mc;
  for(auto l : clause)
  {
    if(l.is_true())
      return;
    if(!l.is_false())
      mc.push(to_minisat(l));
  }
  S.addClause(mc);
}

// ============================================================
// ic3_solvert implementation
// ============================================================

ic3_solvert::ic3_solvert(
  netlistt netlist,
  literalt prop_netlist_lit,
  message_handlert &message_handler)
  : message_handler(message_handler)
{
  // Encode the netlist into CNF: one timeframe only — the next-state
  // functions are nodes in the same variable space.
  base_cnf = std::make_unique<recording_cnft>(solver_message_handler);

  // Take the invariant constraints out of the netlist: unwind() would
  // assert them as unit clauses in base_cnf, which every solver
  // replays. In the lifting solver they would weaken lift()'s
  // implication "cube ∧ inputs ∧ T ⇒ target" to hold only modulo the
  // constraints, admitting constraint-violating states into widened
  // cubes and hence spurious counterexample chains.
  const auto constraints = std::move(netlist.constraints);
  netlist.constraints.clear();

  bmc_mapt bmc_map(netlist, 1, *base_cnf);
  {
    messaget message{solver_message_handler};
    ::unwind(netlist, bmc_map, message, *base_cnf, false, 0);
  }

  prop_current = bmc_map.translate(0, prop_netlist_lit);

  // The initial state constraint, as unit clauses.
  for(auto n : netlist.initial)
  {
    literalt l = bmc_map.translate(0, n);
    if(!l.is_true())
      init_units.push_back(l);
  }

  // Collect latch and input literals.
  for(auto v_it : netlist.var_map.sorted())
  {
    const var_mapt::vart &var = v_it->second;
    if(var.is_latch())
    {
      for(const auto &bit : var.bits)
      {
        literalt current = bmc_map.translate(0, bit.current);
        if(current.is_constant())
          continue;
        literalt next = bmc_map.translate(0, bit.next);
        current_to_latch[current.var_no()] = latches.size();
        latches.push_back({current, next});
      }
    }
    else if(var.is_input() || var.is_nondet())
    {
      for(const auto &bit : var.bits)
      {
        literalt current = bmc_map.translate(0, bit.current);
        if(!current.is_constant())
          input_lits.push_back(current);
      }
    }
  }

  // The conjunction of the invariant constraints, as a literal at the
  // current frame. It is asserted as a unit clause in the frame and
  // init solvers, weakens the property (a bad state must satisfy the
  // constraints), and is added to every lift target, so that the
  // unsatisfiable core proves "cube ∧ inputs ⊨ target ∧ constraints"
  // unconditionally: no widened cube can contain a
  // constraint-violating state. Together this makes every obligation
  // chain a genuine constraint-satisfying counterexample: the initial
  // state satisfies the constraints via the init solver, each lifted
  // cube via its lift core, each unlifted (full-state) cube via the
  // constraint unit in the frame solver that produced it, and the bad
  // state via the weakened property.
  if(!constraints.empty())
  {
    literalt c_all = const_literal(true);
    for(auto c : constraints)
      c_all = base_cnf->land(c_all, bmc_map.translate(0, c));

    if(!c_all.is_true())
    {
      constraint_lit = c_all;

      // weaken the property: bad = c_all ∧ ¬P
      prop_current = base_cnf->lor(!c_all, prop_current);
    }
  }

  lit_activity.resize(latches.size(), 0.0f);

  // Create the initial state solver.
  init_solver =
    std::make_unique<satcheck_no_simplifiert>(solver_message_handler);
  replay_base_cnf(*init_solver, true);
  if(!constraint_lit.is_true())
    init_solver->lcnf({constraint_lit});

  // Create lifting solver using IC3's MiniSAT (has releaseVar).
  lift_minisat = new_minisat_solver();

  // Determine which latches have forced initial values. If all are
  // forced, the initial state is unique and intersection checks
  // become purely syntactic.
  init_values.resize(latches.size(), tvt::unknown());
  if(init_solver->prop_solve(bvt{}) == propt::resultt::P_SATISFIABLE)
  {
    std::vector<bool> model(latches.size());
    for(std::size_t i = 0; i < latches.size(); i++)
      model[i] = init_solver->l_get(latches[i].current).is_true();

    init_is_unique_state = true;
    for(std::size_t i = 0; i < latches.size(); i++)
    {
      bvt assumption = {model[i] ? !latches[i].current : latches[i].current};
      if(init_solver->prop_solve(assumption) == propt::resultt::P_UNSATISFIABLE)
      {
        init_values[i] = tvt(model[i]);
      }
      else
        init_is_unique_state = false;
    }
  }

  // F_0
  frame_clauses.emplace_back();

  messaget message{message_handler};
  message.statistics() << "IC3: " << latches.size() << " latches, "
                       << base_cnf->no_variables() << " variables, "
                       << base_cnf->no_clauses() << " clauses" << messaget::eom;
}

ic3_solvert::~ic3_solvert() = default;

std::size_t ic3_solvert::number_of_frames() const
{
  return frame_clauses.size();
}

std::size_t ic3_solvert::total_clauses() const
{
  std::size_t n = 0;
  for(const auto &f : frame_clauses)
    n += f.size();
  return n;
}

double ic3_solvert::average_clause_size() const
{
  std::size_t n = 0, lits = 0;
  for(const auto &f : frame_clauses)
    for(const auto &c : f)
    {
      n++;
      lits += c.clause.size();
    }
  return n == 0 ? 0.0 : double(lits) / double(n);
}

void ic3_solvert::replay_base_cnf(cnft &dest, bool with_init)
{
  dest.set_no_variables(base_cnf->no_variables());
  for(const auto &clause : base_cnf->get_clauses())
    dest.lcnf(clause);
  if(with_init)
    for(auto l : init_units)
      dest.lcnf({l});
}

literalt ic3_solvert::to_next(literalt l) const
{
  auto it = current_to_latch.find(l.var_no());
  PRECONDITION(it != current_to_latch.end());
  const auto &latch = latches[it->second];
  // l might be positive or negative relative to latch.current
  return latch.next ^ (l.sign() != latch.current.sign());
}

cubet ic3_solvert::extract_state(const IctMinisat::Solver &S)
{
  cubet cube;
  cube.reserve(latches.size());
  for(const auto &latch : latches)
  {
    auto val = S.modelValue(to_minisat(latch.current));
    if(val == IctMinisat::l_True)
      cube.push_back(latch.current);
    else if(val == IctMinisat::l_False)
      cube.push_back(!latch.current);
    // skip don't-care (unknown) bits — smaller cubes
  }
  return cube;
}

void ic3_solvert::new_frame()
{
  frame_clauses.emplace_back();
}

std::unique_ptr<IctMinisat::Solver> ic3_solvert::new_minisat_solver()
{
  auto S = std::make_unique<IctMinisat::Solver>();
  auto nv = base_cnf->no_variables();
  while(S->nVars() < (int)nv)
    S->newVar();
  for(const auto &clause : base_cnf->get_clauses())
    add_minisat_clause(*S, clause);
  // Restrict decisions to latch and input variables. The AIG gates are
  // encoded with the full 3-clause Tseitin AND encoding (both polarities),
  // so once all latch-current and input variables are assigned, BCP
  // implies every internal gate variable; models are thus still total.
  for(IctMinisat::Var v = 0; v < S->nVars(); v++)
    S->setDecisionVar(v, false);
  for(const auto &latch : latches)
    S->setDecisionVar(latch.current.var_no(), true);
  for(auto l : input_lits)
    S->setDecisionVar(l.var_no(), true);
  return S;
}

IctMinisat::Solver &ic3_solvert::get_solver(std::size_t level)
{
  while(frame_solvers.size() <= level)
    frame_solvers.emplace_back();
  auto &fs = frame_solvers[level];
  if(!fs)
  {
    fs = new_minisat_solver();
    if(!constraint_lit.is_true())
      add_minisat_clause(*fs, {constraint_lit});
    if(level == 0)
      for(auto l : init_units)
        add_minisat_clause(*fs, {l});
    for(std::size_t j = level; j < frame_clauses.size(); j++)
      for(const auto &cl : frame_clauses[j])
        add_minisat_clause(*fs, cl.clause);
  }
  return *fs;
}

void ic3_solvert::add_clause(std::size_t level, const clauset &clause)
{
  PRECONDITION(level < frame_clauses.size());

  frame_clauset new_clause(clause);

  // Redundant if subsumed by a clause at the same or a higher level.
  for(std::size_t j = level; j < frame_clauses.size(); j++)
    for(const auto &existing : frame_clauses[j])
      if(subsumes(existing, new_clause))
        return;

  // Remove clauses the new one subsumes; they are at levels <= level,
  // where the new clause is active as well. The subsumed clauses stay
  // in already-built solvers, which is harmless.
  for(std::size_t j = 0; j <= level; j++)
  {
    auto &cls = frame_clauses[j];
    cls.erase(
      std::remove_if(
        cls.begin(),
        cls.end(),
        [&](const frame_clauset &c) { return subsumes(new_clause, c); }),
      cls.end());
  }

  for(std::size_t i = 0; i <= level && i < frame_solvers.size(); i++)
    if(frame_solvers[i])
      add_minisat_clause(*frame_solvers[i], new_clause.clause);

  frame_clauses[level].push_back(std::move(new_clause));
  num_clauses_added++;
}

bool ic3_solvert::is_blocked(const cubet &cube, std::size_t level)
{
  // The cube is blocked iff some frame clause subsumes its negation.
  frame_clauset negated(negate_cube(cube));

  for(std::size_t j = level; j < frame_clauses.size(); j++)
    for(const auto &clause : frame_clauses[j])
      if(subsumes(clause, negated))
        return true;

  return false;
}

bool ic3_solvert::initial_state_is_bad()
{
  bvt assumptions = {!prop_current};
  return init_solver->prop_solve(assumptions) == propt::resultt::P_SATISFIABLE;
}

bool ic3_solvert::init_intersects(const cubet &cube)
{
  // Syntactic check against forced initial values first.
  bool all_bits_known = init_is_unique_state;

  for(auto l : cube)
  {
    auto it = current_to_latch.find(l.var_no());
    if(it == current_to_latch.end())
    {
      all_bits_known = false;
      continue;
    }
    tvt v = init_values[it->second];
    if(v.is_unknown())
    {
      all_bits_known = false;
      continue;
    }
    const auto &latch = latches[it->second];
    bool asserts_true = l.sign() == latch.current.sign();
    if(v.is_true() != asserts_true)
      return false; // contradicts the forced initial value
  }

  if(all_bits_known)
    return true; // consistent with the unique initial state

  // Fall back to the initial-state solver.
  return init_solver->prop_solve(cube) == propt::resultt::P_SATISFIABLE;
}

void ic3_solvert::repair_init(const cubet &cube, cubet &reduced)
{
  if(!init_intersects(reduced))
    return;

  std::unordered_set<unsigned> in_reduced;
  for(auto l : reduced)
    in_reduced.insert(l.get());

  for(auto l : cube)
  {
    if(in_reduced.find(l.get()) != in_reduced.end())
      continue;
    reduced.push_back(l);
    if(!init_intersects(reduced))
      return;
  }

  // cube itself is disjoint from init, so we must have returned above
  UNREACHABLE;
}

cubet ic3_solvert::lift(
  const IctMinisat::Solver &query_solver,
  const cubet &full_state,
  const bvt &target_clause)
{
  auto &S = *lift_minisat;
  using namespace IctMinisat;

  // A tautological target cannot be lifted against.
  for(auto l : target_clause)
    if(l.is_true())
      return full_state;

  // Activation literal for the target clause: act -> target_clause.
  // The negated constraint is part of every target, so that the
  // unsatisfiable core also proves that the lifted cube satisfies the
  // invariant constraints — see the constructor.
  Var act_var = S.newVar();
  Lit act = mkLit(act_var, false);
  {
    vec<Lit> clause;
    clause.push(~act);
    for(auto l : target_clause)
      if(!l.is_false())
        clause.push(to_minisat(l));
    if(!constraint_lit.is_true())
      clause.push(to_minisat(!constraint_lit));
    S.addClause(clause);
  }

  // Solve with act + inputs + state as assumptions
  vec<Lit> assumptions;
  assumptions.push(act);
  for(auto l : input_lits)
  {
    auto val = query_solver.modelValue(to_minisat(l));
    if(val == l_True)
      assumptions.push(to_minisat(l));
    else if(val == l_False)
      assumptions.push(to_minisat(!l));
  }
  for(auto l : full_state)
    assumptions.push(to_minisat(l));

  num_lifts++;
  cubet result;
  if(!S.solve(assumptions))
  {
    // UNSAT — extract minimal state from conflict
    for(auto l : full_state)
    {
      if(S.conflict.has(~to_minisat(l)))
        result.push_back(l);
    }
  }

  // Release activation literal (permanently set ~act, freeing the variable)
  S.releaseVar(~act);

  return result.empty() ? full_state : result;
}

bool ic3_solvert::relative_induction(
  std::size_t level,
  const cubet &cube,
  cubet *predecessor,
  bool lift_predecessor)
{
  // A literal with constant-false next-state function makes the cube
  // trivially unreachable; the solver's conflict would be stale.
  for(auto l : cube)
    if(to_next(l).is_false())
    {
      core = {l};
      repair_init(cube, core);
      return true;
    }

  auto &S = get_solver(level);
  using namespace IctMinisat;

  vec<Lit> assumptions;
  Lit act = lit_Undef;

  if(WITH_NEGATED_CUBE)
  {
    // Activation literal for ¬cube at timeframe 0
    act = mkLit(S.newVar());
    vec<Lit> act_clause;
    act_clause.push(~act);
    for(auto l : cube)
      act_clause.push(to_minisat(!l));
    S.addClause(act_clause);
    assumptions.push(act);
  }

  for(auto l : cube)
  {
    literalt nl = to_next(l);
    if(!nl.is_true())
      assumptions.push(to_minisat(nl));
  }

  num_queries++;
  bool unsat = !S.solve(assumptions);

  if(unsat)
  {
    core.clear();
    for(auto l : cube)
    {
      literalt nl = to_next(l);
      if(!nl.is_true() && S.conflict.has(~to_minisat(nl)))
        core.push_back(l);
    }
    if(core.empty())
      core = cube;
    else
      repair_init(cube, core);
  }
  else if(predecessor != nullptr)
  {
    cubet full_state = extract_state(S);
    if(lift_predecessor)
    {
      // act -> ¬cube'
      bvt target_clause;
      target_clause.reserve(cube.size());
      for(auto l : cube)
        target_clause.push_back(!to_next(l));
      *predecessor = lift(S, full_state, target_clause);
    }
    else
      *predecessor = std::move(full_state);
  }

  if(WITH_NEGATED_CUBE)
  {
    // Release the activation literal
    S.releaseVar(~act);
  }

  return unsat;
}

std::optional<cubet>
ic3_solvert::solve_relative(std::size_t level, const cubet &cube)
{
  cubet predecessor;
  if(relative_induction(level, cube, &predecessor, true))
    return std::nullopt;
  return predecessor;
}

std::optional<cubet> ic3_solvert::solve_bad(std::size_t level)
{
  if(prop_current.is_true())
    return std::nullopt;

  auto &S = get_solver(level);

  IctMinisat::vec<IctMinisat::Lit> assumptions;
  if(!prop_current.is_false())
    assumptions.push(to_minisat(!prop_current));

  num_queries++;
  if(S.solve(assumptions))
  {
    // Lift against the property: act -> prop
    return lift(S, extract_state(S), {prop_current});
  }

  return std::nullopt;
}

bool ic3_solvert::ctg_down(
  std::size_t level,
  cubet &cand,
  std::size_t &ctg_budget)
{
  std::size_t joins = 0;

  while(true)
  {
    if(init_intersects(cand))
      return false;

    cubet predecessor;
    if(relative_induction(level, cand, &predecessor, false))
    {
      cand = core;
      return true;
    }

    // Counterexample-to-generalization: try to block the predecessor.
    // The budget is shared across the enclosing generalize call —
    // unbounded CTG blocking floods the frames with weak clauses.
    if(
      ctg_budget > 0 && level > 0 && !init_intersects(predecessor) &&
      relative_induction(level, predecessor, nullptr, false))
    {
      add_clause(
        std::min(level + 1, frame_clauses.size() - 1), negate_cube(core));
      ctg_budget--;
      continue;
    }

    // Join cand with the predecessor.
    if(++joins > JOIN_MAX)
      return false;
    std::unordered_set<unsigned> pred_lits;
    for(auto l : predecessor)
      pred_lits.insert(l.get());

    cubet joined;
    joined.reserve(cand.size());
    for(auto l : cand)
      if(pred_lits.find(l.get()) != pred_lits.end())
        joined.push_back(l);

    if(joined.empty() || joined.size() >= cand.size())
      return false; // no progress

    cand = std::move(joined);
  }
}

cubet ic3_solvert::generalize(std::size_t level, cubet cube)
{
  std::size_t ctg_budget = CTG_MAX;

  // Sort by activity: drop least-active literals first
  std::sort(
    cube.begin(),
    cube.end(),
    [&](literalt a, literalt b)
    {
      auto ia = current_to_latch.find(a.var_no());
      auto ib = current_to_latch.find(b.var_no());
      float aa =
        (ia != current_to_latch.end()) ? lit_activity[ia->second] : 0.0f;
      float ab =
        (ib != current_to_latch.end()) ? lit_activity[ib->second] : 0.0f;
      return aa < ab;
    });

  // MIC: try dropping each literal, with ctg_down deciding whether the
  // remainder is still relatively inductive. On success, ctg_down has
  // shrunk the candidate further via the unsatisfiable core. Literals
  // are ordered by activity, so after several consecutive failures the
  // remaining literals are unlikely to be droppable — give up early.
  std::size_t i = 0, consecutive_fails = 0;
  while(cube.size() > 1 && i < cube.size() && consecutive_fails < MIC_FAIL_MAX)
  {
    cubet cand;
    cand.reserve(cube.size() - 1);
    for(std::size_t j = 0; j < cube.size(); j++)
      if(j != i)
        cand.push_back(cube[j]);

    if(ctg_down(level, cand, ctg_budget))
    {
      cube = std::move(cand); // retry at the same index
      consecutive_fails = 0;
    }
    else
    {
      i++;
      consecutive_fails++;
    }
  }

  // Bump activity for literals that survived generalization
  for(auto l : cube)
  {
    auto it = current_to_latch.find(l.var_no());
    if(it != current_to_latch.end())
      lit_activity[it->second] += 1.0f;
  }

  return cube;
}

bool ic3_solvert::propagate()
{
  for(std::size_t i = 1; i + 1 < frame_clauses.size(); i++)
  {
    // The clauses of F_i's delta; a copy, since pushing mutates the frame.
    auto clauses = frame_clauses[i];

    for(const auto &fc : clauses)
    {
      // The clause itself is in the level-i solver already, so the
      // query F_i ∧ T ∧ cube' needs no activation literal.
      auto &S = get_solver(i);
      cubet cube = negate_cube(fc.clause);

      bool trivially_unsat = false;
      IctMinisat::vec<IctMinisat::Lit> assumptions;
      for(auto l : cube)
      {
        literalt nl = to_next(l);
        if(nl.is_false())
        {
          trivially_unsat = true;
          break;
        }
        if(!nl.is_true())
          assumptions.push(to_minisat(nl));
      }

      num_queries++;
      if(trivially_unsat || !S.solve(assumptions))
      {
        // Holds at F_{i+1}: move the delta entry up. The solvers at
        // levels <= i contain the clause already; only level i+1 needs it.
        auto &cls = frame_clauses[i];
        auto it = std::find(cls.begin(), cls.end(), fc);
        if(it != cls.end())
          cls.erase(it);

        if(i + 1 < frame_solvers.size() && frame_solvers[i + 1])
          add_minisat_clause(*frame_solvers[i + 1], fc.clause);
        frame_clauses[i + 1].push_back(fc);
      }
    }

    if(frame_clauses[i].empty())
      return true; // F_i = F_{i+1}: inductive invariant found
  }

  return false;
}

// ============================================================
// Main IC3 algorithm
// ============================================================

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

ic3_resultt ic3_solvert::solve()
{
  messaget message{message_handler};

  auto start_time = std::chrono::steady_clock::now();

  // Check: can initial states violate the property?
  if(initial_state_is_bad())
  {
    message.result() << "Property violated in initial state" << messaget::eom;
    return ic3_resultt::REFUTED;
  }

  while(true)
  {
    new_frame();
    std::size_t k = number_of_frames() - 1;

    message.progress() << "IC3: frame " << k << " (" << num_queries
                       << " queries, " << num_lifts << " lifts, "
                       << total_clauses() << " clauses, avg size "
                       << average_clause_size() << ")" << messaget::eom;

    std::priority_queue<
      proof_obligationt,
      std::vector<proof_obligationt>,
      std::greater<proof_obligationt>>
      obligations;

    // Blocking phase
    while(true)
    {
      auto bad_cube = solve_bad(k);
      if(!bad_cube.has_value())
        break;

      obligations.push({bad_cube.value(), k});

      while(!obligations.empty())
      {
        auto [cube, level] = obligations.top();
        obligations.pop();

        if(is_blocked(cube, level))
          continue;

        if(init_intersects(cube))
        {
          message.result() << "Property refuted" << messaget::eom;
          return ic3_resultt::REFUTED;
        }

        if(level == 0)
        {
          add_clause(0, negate_cube(cube));
          continue;
        }

        auto pred = solve_relative(level - 1, cube);
        if(pred.has_value())
        {
          obligations.push({pred.value(), level - 1});
          obligations.push({std::move(cube), level});
        }
        else
        {
          cubet generalized = generalize(level - 1, core);

          // Eagerly push the generalized clause to the highest frame where
          // it is still relatively inductive: one query per level, instead
          // of a full re-generalization when the obligation is re-queued.
          std::size_t push_to = level;
          while(push_to < k &&
                relative_induction(push_to, generalized, nullptr, false))
          {
            push_to++;
          }

          add_clause(push_to, negate_cube(generalized));

          if(push_to + 1 <= k)
            obligations.push({std::move(cube), push_to + 1});
        }
      }
    } // end blocking phase

    // Propagation: push clauses from F_i to F_{i+1}
    if(propagate())
    {
      auto end_time = std::chrono::steady_clock::now();
      message.statistics()
        << "IC3: converged at frame " << k << " in "
        << std::chrono::duration<double>(end_time - start_time).count()
        << " seconds (" << num_queries << " queries)" << messaget::eom;
      return ic3_resultt::PROVED;
    }
  }
}
