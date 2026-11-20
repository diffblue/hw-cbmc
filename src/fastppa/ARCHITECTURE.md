How fastppa computes an estimate
================================

Input
-----

`fastppa_frontend.cpp` uses EBMC's Verilog front end to build a
transition system. Its state constraints define wires and outputs
(`w == expr`, or several equalities for separately assigned parts of a
wire), its transition constraints define the next state of each register
(`next(r) == expr`). The top module's output ports are the roots of the
estimate.

The graph (`estimate.cpp`)
--------------------------

`grapht` builds one graph over all definitions:

- Wires are inlined. A constant select from a wire whose definition is an
  array or a concatenation resolves to the selected part, so that parts of
  a wire may depend on other parts of it.
- Nodes are hash-consed: the same operator on the same operands is one
  node, wherever it occurs. The operands of commutative operators are
  sorted.
- Leaves are inputs, registers, constants, and opaque values (undriven
  wires, registers that are never updated).
- Constants are propagated with `simplify_expr`, also through wires and
  through registers whose next state is a constant or the register itself;
  finding such a register can make others constant, so the graph is
  rebuilt until nothing changes.
- Unsupported operators and types without a width (e.g. `real`) are
  errors.

Costing
-------

`costert` costs the nodes that reach an output, directly or through
registers (the cone of influence), each once:

- The cost of an operator of width w (and, for array accesses, n
  elements) comes from the cost table: area = a0 + a1·F(w, n), delay = d0
  + d1·G(w, n), switching energy and leakage with the form of the area.
- A chain of the same associative operator (`+ * & | ^`) whose inner nodes
  have a single use is one n-ary operator: n−1 operators of area, built as
  a tree balanced by the arrival times of the leaves.
- Rules that hold for any synthesis tool:
  - shifts, bit selects and array indices by constants are wiring;
  - a bitwise operator with a constant only needs gates for the bits the
    constant does not decide; a mux with a constant input is a gate per
    bit; a multiplication by a power of two is wiring;
  - operations with a constant operand (`+`, `*`, `==`, `<`) have their
    own, cheaper, cost functions;
  - `x[i*W +: W]`, which arrives as a shift of x by i·W followed by a
    constant select, is a W-bit mux of the slots of x;
  - a shift by a distance whose low k bits are known to be zero has k
    fewer stages;
  - `c ? (m WITH i:=v) : m` gates the write enables, rather than muxing
    the whole array.
- Timing is a longest-path computation: inputs arrive at 0, registers at
  their clock-to-Q delay, and every operator adds its delay. The critical
  path is the latest arrival at an output or register input. The path to
  each endpoint is traced back for the report.

The `--netlist` estimator (`fastppa_estimator.cpp`)
---------------------------------------------------

The transition system is bit-blasted into an AIG. The AND gates and
latches in the cone of influence of the outputs are counted. Division and
array accesses are encoded relationally: their results are fresh variables
constrained by the AIG's constraints, which are therefore added to the
cone when such a variable is reached, and the variable arrives when its
constraints do. Area, energy and leakage are per AND gate and per latch;
delay is the longest path in AND gates times a fitted delay per gate.

Cost tables (`cost_table.cpp`)
------------------------------

Each table lists, per operator kind, the forms and coefficients of area,
delay, switching energy and leakage, plus the clock-pin energy of a
register bit (`clock`) and the costs of one AIG AND gate (`aig_and`). The
measured tables are fitted by `benchmarking/fastppa_eval/fit.py` on
designs with a single operator each, synthesized to the library; for each
kind, the form is the one with the smallest leave-one-out error. The
derived tables are produced by `derive.py` (see
`benchmarking/fastppa_eval/PROCESS_NODES.md`). All tables are compiled
in; `make_tables.sh` regenerates them.

Power
-----

    dynamic = data_energy · toggle_rate · f
    clock   = clock_energy · f
    leakage = Σ leakage of operators and registers

`data_energy` is the switching energy per cycle at a toggle rate of 1, so
the toggle rate scales only the data part; the clock pins of the
registers toggle every cycle. There is no clock-tree model.
