# AGENTS.md — Guide for AI Coding Agents

This file helps AI coding agents (Claude Code, Kiro, Copilot, etc.) work
effectively with this codebase.

---

## Project Overview

**EBMC** (Enhanced Bounded Model Checker) is a formal verification tool for
hardware designs. It verifies LTL (Linear Temporal Logic) properties and
SystemVerilog Assertions (SVA) against hardware circuits described in:

- Verilog 2005 / SystemVerilog 2017
- NuSMV (`.smv` files)
- ISCAS89 netlist format

The companion tool **hw-cbmc** generates C software interfaces for hardware
designs, enabling software model checking of hardware/software systems.

This codebase is a C++17 project. It depends on **CBMC** (as a git submodule
at `lib/cbmc/`) and extends CBMC with hardware-specific functionality.

---

## Repository Layout

```
hw-cbmc/
├── src/                    # All source code
│   ├── ebmc/               # Main EBMC tool (entry point: main.cpp)
│   ├── hw-cbmc/            # hw-cbmc tool (interface generation)
│   ├── verilog/            # Verilog/SystemVerilog parser & type checker
│   ├── vhdl/               # VHDL language support
│   ├── smvlang/            # NuSMV model language support
│   ├── temporal-logic/     # LTL and SVA handling
│   ├── trans-word-level/   # Word-level transition system transformations
│   ├── trans-netlist/      # Netlist transformations
│   ├── aiger/              # AIGER format support
│   ├── ic3/                # IC3 unbounded model checker
│   ├── vlindex/            # Verilog indexer tool
│   ├── util/               # Shared utility functions
│   └── Makefile            # Top-level build file for all tools
├── regression/             # Regression test suites
│   ├── ebmc/               # Tests for the EBMC engine
│   ├── verilog/            # Tests for Verilog/SystemVerilog input
│   ├── smv/                # Tests for SMV input
│   └── vlindex/            # Tests for the Verilog indexer
├── unit/                   # Unit tests (built with `make -C unit`)
├── lib/
│   └── cbmc/               # CBMC dependency (git submodule)
└── .github/workflows/      # CI configuration
```

---

## Building

### Prerequisites

- g++ 7.0+ or Clang 19+
- GNU Make 3.81+
- Flex and Bison
- Z3 (optional, for SMT-based solving)

### First-time setup

```bash
git submodule update --init
make -C lib/cbmc/src minisat2-download
make -C lib/cbmc/src cadical-download
```

### Build all tools

```bash
make -C src
# or parallel:
make -C src -j4
```

Compiled binaries:
- `src/ebmc/ebmc`
- `src/hw-cbmc/hw-cbmc`
- `src/vlindex/vlindex`

### Incremental builds

Each subdirectory has its own Makefile. You can rebuild a single component:

```bash
make -C src/verilog
```

---

## Testing

### Unit tests

```bash
make -C unit
```

### Regression tests

```bash
make -C regression/ebmc test         # SAT-based
make -C regression/ebmc test-z3      # Z3-based

make -C regression/verilog test
make -C regression/verilog test-z3

make -C regression/smv test
make -C regression/smv test-z3
make -C regression/vlindex test
```

Run all regression tests (matches CI):

```bash
make -C regression/ebmc test test-z3
make -C regression/verilog test test-z3
make -C regression/smv test test-z3
make -C regression/vlindex test
```

### Test descriptor format

Regression tests use `.desc` files. Example:

```
CORE buechi
case1.sv
--buechi --bound 20 --numbered-trace
^\[main\.p0\] always \(.*\): REFUTED$
^Counterexample with 11 states:$
^EXIT=10$
^SIGNAL=0$
```

Fields:
1. Test category (`CORE`, `KNOWNBUG`, `FUTURE`)
2. Input file
3. Command-line arguments
4. Expected output lines (regex, anchored with `^`)
5. `EXIT=N` — expected exit code
6. `SIGNAL=0` — expected signal

`KNOWNBUG` tests are known failures and are skipped. `FUTURE` tests are
planned but not yet implemented.

---

## Coding Conventions

### Language standard

C++17.

### Formatting

Configured via `.clang-format` (symlinked from CBMC). Always run
`clang-format` on modified files. The CI enforces this via
`.github/workflows/syntax-checks.yaml`.

### Style rules

- **Indentation:** 2 spaces, no tabs
- **Line length:** 80 columns
- **Pointer/reference alignment:** right-aligned (`int *p`, `int &r`)
- **Brace style:** Allman (opening brace on its own line)
- **Naming:**
  - Class names end with `t`: `verilog_typecheckt`, `ebmc_parse_optionst`
  - Include guards: `CPROVER_<DIRECTORY>_<FILE>_H` (all caps)
  - Free functions and methods: lowercase with underscores
  - Use `PRECONDITION(...)` and `POSTCONDITION(...)` from `<util/invariant.h>`

### File header template

```cpp
/*******************************************************************\

Module: <Module Name>

Author: <Name>, <email>

\*******************************************************************/
```

### Include guards

```cpp
#ifndef CPROVER_VERILOG_VERILOG_TYPECHECK_H
#define CPROVER_VERILOG_VERILOG_TYPECHECK_H
// ...
#endif // CPROVER_VERILOG_VERILOG_TYPECHECK_H
```

### IREP / expression conventions

This codebase uses CBMC's `irept`/`exprt`/`typet` IR. Key points:
- Custom IREP IDs are declared in `src/hw_cbmc_irep_ids.h`
- Use `.get(ID_...)`, `.set(ID_...)` for IREP attribute access
- Prefer typed accessors (`to_symbol_expr(...)`, etc.) over raw casts

---

## Key Architectural Concepts

- **Transition system:** A hardware design is represented as a transition
  system with initial states, a state-space type, and a transition relation.
  See `src/trans-word-level/` and `src/trans-netlist/`.
- **Netlist:** A Boolean gate-level representation. The `aig_` prefix
  indicates And-Inverter Graph nodes.
- **BMC:** Bounded model checking unrolls the transition relation for
  `--bound N` steps and hands the formula to a SAT/SMT solver.
- **Buechi:** LTL is converted to a Buechi automaton and combined with the
  design for liveness property checking.
- **IC3/PDR:** Unbounded model checking via `src/ic3/`.
- **SVA:** SystemVerilog Assertions are parsed by the Verilog front-end and
  lowered to temporal logic. See `src/temporal-logic/`.

---

## Dependencies on CBMC

`lib/cbmc/` is a git submodule. Never edit files inside `lib/cbmc/` — changes
must go to the upstream CBMC repository. When CBMC is updated, run:

```bash
git submodule update
make -C src
```

The build system automatically links against CBMC libraries including
`util`, `solvers`, `big-int`, and language modules.

---

## Git Conventions

Commit message style from recent history:

```
Component: Brief imperative description

Longer explanation if needed. Reference IEEE 1800-2017 sections when
relevant (e.g., "Per 1800-2017 section A.9.3, ...").
```

Examples:
- `Verilog: package-scoped function calls`
- `SMV: support for range types in module parameters`
- `KNOWNBUG test for function and task in a package`

Branch names follow `username/short-description` and are submitted as
GitHub pull requests against `main`.

---

## CI

GitHub Actions workflows (`.github/workflows/`):

| Workflow | Trigger | What it does |
|---|---|---|
| `pull-request-checks.yaml` | PRs | Build + unit + regression tests (GCC & Clang) |
| `syntax-checks.yaml` | PRs | `clang-format` check |
| `ebmc-release.yaml` | Tags/manual | Release builds |

The CI uses `ccache` for faster incremental builds.

---

## Common Tasks

### Add a new Verilog language feature

1. Extend the grammar in `src/verilog/verilog_parser.y`
2. Regenerate with `make -C src/verilog` (runs Bison/Flex automatically)
3. Add type-checking logic in `src/verilog/verilog_typecheck*.cpp`
4. Add lowering/elaboration in `src/verilog/verilog_lowering.cpp`
5. Add a regression test in `regression/verilog/`

### Add a new temporal logic operator

1. Extend the AST in `src/temporal-logic/`
2. Update the conversion to automaton in `ltl_to_automaton.cpp` or SVA
   lowering in `sva_to_ltl.cpp`
3. Add tests in `regression/verilog/SVA/`

### Add a new EBMC command-line option

1. Declare the option in `src/ebmc/ebmc_parse_options.h`
2. Parse and dispatch in `src/ebmc/ebmc_parse_options.cpp`
3. Implement in an appropriate engine file under `src/ebmc/`
