# pyebmc — Python Bindings for EBMC

## Design Document (RFC)

**Status:** Request for Comments  
**Date:** 2026-05-10

### Goals

1. Provide a Pythonic API for EBMC that feels natural to EDA engineers
   accustomed to Tcl-based tool scripting (Cadence, Synopsys, Mentor).
2. Follow standard Python conventions (PEP 8, context managers, iterators,
   properties, exceptions).
3. Mirror the EDA Tcl idiom of imperative "command" calls that configure and
   query a persistent session/database, while wrapping them in proper Python
   objects.

### Design Principles

| EDA Tcl Convention | pyebmc Python Equivalent |
|-|-|
| Global tool database / session | `ebmc.Design` object (explicit session) |
| `read_verilog`, `read_hdl` commands | `design.read_verilog(...)` methods |
| `set_top`, `elaborate` | `design.set_top(...)`, `design.elaborate()` |
| `check_property`, `prove` | `design.check_property(...)` |
| `report_*` commands | `design.report_properties()`, iteration |
| `-option value` flags | Keyword arguments |
| Return status codes | Exceptions + result enums |
| `get_*` / `set_*` attribute queries | Python `@property` accessors |

---

## Package Structure

```
pyebmc/
├── __init__.py          # Public API re-exports (Design, Property, etc.)
├── design.py            # Design class (the session object)
├── property.py          # Property / PropertyResult data classes
├── trace.py             # Trace / Waveform access
├── module.py            # Module introspection
├── exceptions.py        # Exception hierarchy
├── cprover/             # CBMC-derived IR types (separate namespace)
│   ├── __init__.py      # Re-exports Expr, Type, SourceLocation
│   ├── expr.py          # Expr class and subclass registry
│   └── type.py          # Type class and subclass registry
├── _engine.py           # Low-level C++ binding (pybind11)
└── py.typed             # PEP 561 marker
```

The `pyebmc.cprover` subpackage contains types originating from the CBMC
intermediate representation (`exprt`, `typet`, `source_locationt`). These
are general-purpose IR nodes not specific to EBMC. The top-level `pyebmc`
namespace contains EBMC-specific objects (`Design`, `Property`, `Trace`,
etc.).

> **Note:** The `pyebmc.cprover` subpackage is intended to eventually move
> into its own standalone package (e.g. `pycprover`) that can be shared
> across CBMC-based tools. For now it ships inside `pyebmc` to simplify
> initial development and distribution.

---

## Core API

### Session: `Design`

The central object, analogous to a Tcl tool session. All state lives here.

```python
import pyebmc

# Create a session (like opening a tool shell)
design = pyebmc.Design()

# --- Reading sources (like read_verilog / read_file) ---
design.read_verilog("alu.sv")
design.read_verilog("top.sv", systemverilog=True)
design.read_smv("model.smv")

# --- Elaboration (like elaborate / set_top) ---
design.set_top("top")
design.elaborate()

# --- Accessing the design hierarchy ---
for mod in design.modules:
    print(mod.name, mod.file, mod.line)

# --- Properties ---
for prop in design.properties:
    print(prop.name, prop.expression, prop.status)
```

#### Constructor

```python
class Design:
    def __init__(
        self,
        *,
        verbosity: int = 2,
        solver: str = "minisat",   # "minisat", "cadical", "z3", "bitwuzla"
    ) -> None: ...
```

#### Source Reading Commands

These mirror the Tcl `read_*` family. The Tcl `set_include_path` and
`set_define` session commands are handled as keyword arguments to
`read_verilog` instead, keeping configuration explicit and per-call:

```python
def read_verilog(
    self,
    path: str | Path,
    *,
    systemverilog: bool = False,
    defines: dict[str, str] | None = None,
    include_dirs: list[str | Path] | None = None,
) -> None: ...

def read_verilog_string(
    self,
    source: str,
    *,
    systemverilog: bool = False,
    filename: str = "<string>",
    defines: dict[str, str] | None = None,
) -> None:
    """Read Verilog/SystemVerilog source from a Python string."""
    ...

def read_smv(self, path: str | Path) -> None: ...
```

#### Elaboration Commands

```python
def set_top(self, module_name: str) -> None: ...

def elaborate(self) -> None:
    """Elaborate the design. Raises ElaborationError on failure."""
    ...

def set_reset(
    self,
    signal: str,
    *,
    active_high: bool = True,
    cycles: int = 1,
) -> None:
    """Define the reset sequence for verification.
    Mirrors the Tcl set_reset_sequence idiom."""
    ...
```

#### Verification Commands

The core "prove" / "check" commands, matching the EDA idiom of running
analysis on the current design state:

```python
def check_property(
    self,
    *,
    bound: int = 10,
    property: str | None = None,   # specific property identifier
    engine: str = "bmc",           # "bmc", "k-induction", "k-induction-step", "ic3", "bdd", "buechi"
    solver: str | None = None,     # override session solver
) -> "ProveResult": ...
```

#### Constraints

```python
def add_constraint(
    self,
    expression: str,
    *,
    step: int | None = None,
) -> None:
    """Add a constraint to the verification.
    If step is given, the constraint applies only at that time frame.
    Otherwise it applies at all time frames."""
    ...
```

#### Property Management

```python
def add_property(
    self,
    name: str,
    expression: str,
) -> None:
    """Add a property from a script (SVA expression string)."""
    ...

def add_property_expr(
    self,
    name: str,
    expression: "Expr",
) -> None:
    """Add a property from a programmatically constructed Expr tree."""
    ...

def disable_property(self, name: str) -> None:
    """Disable a property so it is excluded from verification."""
    ...

def enable_property(self, name: str) -> None:
    """Re-enable a previously disabled property."""
    ...
```

#### Trace / Waveform Access

```python
def get_trace(self, property: str) -> "Trace | None":
    """Get counterexample trace for a refuted property."""
    ...

def random_traces(
    self,
    *,
    count: int = 1,
    steps: int = 10,
    seed: int | None = None,
) -> list["Trace"]: ...

def write_vcd(self, path: str | Path, property: str) -> None:
    """Write counterexample as VCD waveform file."""
    ...
```

#### Reporting Commands

```python
def report_properties(self, *, format: str = "text") -> str:
    """Return formatted property report. format: 'text', 'json', 'xml'."""
    ...

def report_modules(self, *, format: str = "text") -> str: ...
```

#### State Query Properties

```python
@property
def modules(self) -> list["Module"]: ...

@property
def properties(self) -> list["Property"]: ...

@property
def state_variables(self) -> list[str]: ...

@property
def inputs(self) -> list[str]: ...
```

---

### Data Classes

#### `Module`

```python
@dataclass(frozen=True)
class Module:
    name: str
    identifier: str
    mode: str              # "Verilog", "SMV", etc.
    file: str | None
    line: int | None
```

#### `Property`

```python
from pyebmc.cprover import Expr

@dataclass
class Property:
    name: str
    identifier: str
    expr: Expr             # structured expression tree (see cprover.Expr)
    status: PropertyStatus
    bound: int | None
    failure_reason: str | None
    proof_method: str | None

    @property
    def expression(self) -> str:
        """Human-readable rendering of the property expression."""
        return str(self.expr)

    @property
    def proved(self) -> bool: ...

    @property
    def refuted(self) -> bool: ...

    @property
    def has_trace(self) -> bool: ...
```

#### `PropertyStatus` (Enum)

```python
class PropertyStatus(enum.Enum):
    UNKNOWN = "unknown"
    PROVED = "proved"
    PROVED_WITH_BOUND = "proved_with_bound"
    REFUTED = "refuted"
    REFUTED_WITH_BOUND = "refuted_with_bound"
    DISABLED = "disabled"
    ASSUMED = "assumed"
    UNSUPPORTED = "unsupported"
    DROPPED = "dropped"
    FAILURE = "failure"
    INCONCLUSIVE = "inconclusive"
```

#### `ProveResult`

```python
@dataclass(frozen=True)
class ProveResult:
    properties: list[Property]

    @property
    def all_proved(self) -> bool: ...

    @property
    def has_counterexample(self) -> bool: ...

    def __bool__(self) -> bool:
        """True if all properties proved (enables `if design.check_property(): ...`)."""
        return self.all_proved
```

#### `Trace`

```python
@dataclass(frozen=True)
class Trace:
    steps: int
    signals: list[str]

    def value(self, signal: str, step: int) -> str:
        """Get signal value at a given time step."""
        ...

    def values(self, signal: str) -> list[str]:
        """Get all values of a signal across time."""
        ...

    def to_vcd(self) -> str:
        """Render trace as VCD string."""
        ...

    def to_dict(self) -> dict[str, list[str]]:
        """Signal name -> list of values per step."""
        ...
```

---

### Exceptions

```python
class EbmcError(Exception):
    """Base exception for all pyebmc errors."""

class ParseError(EbmcError):
    """Raised when source file parsing fails."""
    file: str | None
    line: int | None
    message: str

class ElaborationError(EbmcError):
    """Raised when elaboration fails."""

class SolverError(EbmcError):
    """Raised when the solver encounters an error."""

class PropertyNotFoundError(EbmcError, KeyError):
    """Raised when referencing a non-existent property."""
```

---

## Usage Examples

### Example 1: Basic BMC (mirrors Tcl `read_verilog` / `check_property` flow)

```python
import pyebmc

design = pyebmc.Design(solver="cadical")
design.read_verilog("top.sv", systemverilog=True)
design.set_top("top")
design.elaborate()

result = design.check_property(bound=20)

if result:
    print("All properties proved within bound 20")
else:
    for prop in result.properties:
        if prop.refuted:
            print(f"FAIL: {prop.name} — {prop.failure_reason}")
            trace = design.get_trace(prop.identifier)
            design.write_vcd(f"{prop.name}.vcd", prop.identifier)
```

### Example 2: Unbounded verification with IC3

```python
design = pyebmc.Design(solver="minisat")
design.read_verilog("counter.sv", systemverilog=True)
design.set_top("counter")
design.elaborate()

result = design.check_property(engine="ic3")
assert result.all_proved
```

### Example 3: K-induction with 5 time frames

```python
design = pyebmc.Design()
design.read_verilog("arbiter.sv", systemverilog=True)
design.set_top("arbiter")
design.elaborate()

# Base case: check no counterexample exists within 5 steps
base = design.check_property(bound=5, engine="bmc")
if not base:
    print("Counterexample found in base case")
else:
    # Step case: check the inductive step at k=5
    step = design.check_property(bound=5, engine="k-induction-step")
    if step:
        print("Property proved by induction with k=5")
    else:
        print("Induction step failed — try increasing bound")
```

### Example 4: BMC with a custom constraint

```python
design = pyebmc.Design()
design.read_verilog_string("""
module counter(input clk);
  reg [3:0] cnt;
  initial cnt = 0;
  always @(posedge clk) cnt <= cnt + 1;
  p1: assert property (@(posedge clk) cnt <= 10);
endmodule
""", systemverilog=True)
design.set_top("counter")
design.elaborate()

# Constrain cnt to increment from 0 to 10 across time frames
for step in range(11):
    design.add_constraint(f"counter.cnt == {step}", step=step)

result = design.check_property(bound=10)
if result:
    print("Property holds under the constrained counter sequence")
```

### Example 5: Iterative deepening (common EDA scripting pattern)

```python
design = pyebmc.Design()
design.read_verilog("fifo.sv", systemverilog=True)
design.set_top("fifo")
design.elaborate()

for bound in [5, 10, 20, 50]:
    result = design.check_property(bound=bound, engine="bmc")
    if not result.has_counterexample:
        print(f"No bugs found up to bound {bound}")
    else:
        break
```

### Example 6: Random trace generation (test stimulus)

```python
design = pyebmc.Design()
design.read_verilog("dut.sv", systemverilog=True)
design.set_top("dut")
design.elaborate()

traces = design.random_traces(count=100, steps=50, seed=42)
for i, trace in enumerate(traces):
    with open(f"trace_{i}.vcd", "w") as f:
        f.write(trace.to_vcd())
```

### Example 7: Design introspection (like Tcl `get_ports`, `get_cells`)

```python
design = pyebmc.Design()
design.read_verilog("chip.sv", systemverilog=True)
design.set_top("chip")
design.elaborate()

print("Modules:", [m.name for m in design.modules])
print("Inputs:", design.inputs)
print("State variables:", design.state_variables)

# Iterate properties with expression access
for prop in design.properties:
    print(f"{prop.name}: {prop.expression}")
    print(f"  expr id: {prop.expr.id}, type: {prop.expr.type}")
    for op in prop.expr:
        print(f"    operand: {op.id}")
```

---

## Expr and Type Bindings (`pyebmc.cprover`)

This section describes the Python bindings for CBMC's `exprt` and `typet`
intermediate representation, exposed under the `pyebmc.cprover` namespace.
These are general-purpose IR types originating from the CBMC framework — not
EBMC-specific — and are therefore separated into their own subpackage.

The bindings expose them as immutable, tree-structured Python objects that
support iteration, pattern matching, and pretty-printing.

### Design Rationale

CBMC's IR is a tree of `irept` nodes. Each node has:
- An **id** (a string tag identifying the node kind, e.g. `"and"`, `"symbol"`, `"constant"`)
- **Named sub-nodes** (key-value attributes, e.g. `ID_type`, `ID_identifier`)
- **Unnamed sub-nodes** (ordered children / operands)

The Python bindings mirror this structure faithfully, allowing users to
traverse and inspect property expressions programmatically — essential for
EDA scripting workflows that filter, transform, or report on assertions.

Placing these in `pyebmc.cprover` keeps the namespace clean: EBMC-specific
objects (`Design`, `Property`, `Trace`) live at the top level, while the
underlying IR types are accessed via:

```python
from pyebmc.cprover import Expr, Type, SourceLocation
```

### Package Location

```
pyebmc/cprover/
├── __init__.py      # Re-exports Expr, Type, SourceLocation
├── expr.py          # Expr class, subclasses, and registry
└── type.py          # Type class and subclasses
```

---

### `cprover.Expr` — Expression Tree Node

```python
# pyebmc/cprover/expr.py

class Expr:
    """Immutable expression node. Wraps CBMC's exprt."""

    @property
    def id(self) -> str:
        """Node kind identifier (e.g. 'and', 'not', 'symbol', 'constant',
        'sva_always', 'G', 'U', etc.)."""
        ...

    @property
    def type(self) -> "Type":
        """The type of this expression."""
        ...

    @property
    def operands(self) -> tuple["Expr", ...]:
        """Ordered child expressions (immutable tuple)."""
        ...

    # --- Iteration (enables `for op in expr`) ---

    def __iter__(self) -> Iterator["Expr"]:
        """Iterate over direct operands."""
        return iter(self.operands)

    def __len__(self) -> int:
        """Number of direct operands."""
        return len(self.operands)

    def __getitem__(self, index: int) -> "Expr":
        """Access operand by index."""
        return self.operands[index]

    # --- Named attribute access ---

    def get(self, key: str) -> str | None:
        """Get a named attribute (named_sub) by key.
        Returns None if not present."""
        ...

    def __contains__(self, key: str) -> bool:
        """Check if a named attribute exists."""
        ...

    # --- Pretty-printing ---

    def __str__(self) -> str:
        """Human-readable rendering (Verilog/SVA syntax where possible)."""
        ...

    def __repr__(self) -> str:
        """Debug representation showing the IR structure."""
        ...

    # --- Structural equality and hashing ---

    def __eq__(self, other: object) -> bool: ...
    def __hash__(self) -> int: ...

    # --- Tree traversal ---

    def depth_first(self) -> Iterator["Expr"]:
        """Pre-order depth-first traversal of the entire expression tree."""
        yield self
        for op in self.operands:
            yield from op.depth_first()

    def find(self, expr_id: str) -> Iterator["Expr"]:
        """Yield all sub-expressions with the given id."""
        for node in self.depth_first():
            if node.id == expr_id:
                yield node

    # --- Convenience predicates ---

    @property
    def is_constant(self) -> bool:
        return self.id == "constant"

    @property
    def is_symbol(self) -> bool:
        return self.id == "symbol"

    @property
    def is_boolean(self) -> bool:
        return self.type.id == "bool"

    # --- Source location ---

    @property
    def source_location(self) -> "SourceLocation | None":
        """Source file/line where this expression was defined, if available."""
        ...
```

#### Symbol-specific accessors

```python
class SymbolExpr(Expr):
    """Specialization for symbol expressions (id == 'symbol')."""

    @property
    def identifier(self) -> str:
        """The full symbol identifier (e.g. 'main.cnt1')."""
        ...

    @property
    def display_name(self) -> str:
        """Short display name."""
        ...
```

#### Constant-specific accessors

```python
class ConstantExpr(Expr):
    """Specialization for constant expressions (id == 'constant')."""

    @property
    def value(self) -> str:
        """The constant value as a string (binary for bitvectors)."""
        ...

    def as_int(self) -> int:
        """Interpret the constant as a Python integer."""
        ...
```

#### Temporal / SVA expression accessors

```python
class SvaAlwaysExpr(Expr):
    """SVA 'always' property (id == 'sva_always')."""

    @property
    def property(self) -> Expr:
        """The sub-property under 'always'."""
        return self.operands[0]


class SvaEventuallyExpr(Expr):
    """SVA 's_eventually' / 'eventually' (id == 'sva_s_eventually')."""

    @property
    def property(self) -> Expr:
        return self.operands[0]


class GExpr(Expr):
    """LTL 'G' (globally) operator."""

    @property
    def property(self) -> Expr:
        return self.operands[0]


class FExpr(Expr):
    """LTL 'F' (finally/eventually) operator."""

    @property
    def property(self) -> Expr:
        return self.operands[0]


class UExpr(Expr):
    """LTL 'U' (until) operator."""

    @property
    def left(self) -> Expr:
        return self.operands[0]

    @property
    def right(self) -> Expr:
        return self.operands[1]
```

---

### `cprover.Type` — Type Node

```python
# pyebmc/cprover/type.py

class Type:
    """Immutable type node. Wraps CBMC's typet."""

    @property
    def id(self) -> str:
        """Type kind identifier (e.g. 'bool', 'unsignedbv', 'signedbv',
        'array', 'struct')."""
        ...

    @property
    def subtypes(self) -> tuple["Type", ...]:
        """Sub-types (e.g. element type of an array)."""
        ...

    # --- Named attribute access ---

    def get(self, key: str) -> str | None:
        """Get a named attribute by key (e.g. 'width' for bitvectors)."""
        ...

    # --- Convenience accessors ---

    @property
    def width(self) -> int | None:
        """Bit width for bitvector types. None for non-bitvector types."""
        w = self.get("width")
        return int(w) if w is not None else None

    @property
    def is_bool(self) -> bool:
        return self.id == "bool"

    @property
    def is_signed(self) -> bool:
        return self.id == "signedbv"

    @property
    def is_unsigned(self) -> bool:
        return self.id == "unsignedbv"

    # --- Pretty-printing ---

    def __str__(self) -> str:
        """Human-readable type string (e.g. 'bit[7:0]', 'bool')."""
        ...

    def __repr__(self) -> str: ...
    def __eq__(self, other: object) -> bool: ...
    def __hash__(self) -> int: ...
```

#### Bitvector type specialization

```python
class UnsignedBvType(Type):
    """Unsigned bitvector type (id == 'unsignedbv')."""

    @property
    def width(self) -> int: ...


class SignedBvType(Type):
    """Signed bitvector type (id == 'signedbv')."""

    @property
    def width(self) -> int: ...


class ArrayType(Type):
    """Array type (id == 'array')."""

    @property
    def element_type(self) -> Type: ...

    @property
    def size(self) -> Expr:
        """Array size expression."""
        ...
```

---

### `cprover.SourceLocation`

```python
# pyebmc/cprover/expr.py (co-located with Expr)

@dataclass(frozen=True)
class SourceLocation:
    file: str | None
    line: int | None
    column: int | None
    function: str | None
```

---

### Property Iteration with Expression Access

The `Property.expr` field exposes the full `cprover.Expr` tree, enabling
programmatic inspection:

```python
import pyebmc

design = pyebmc.Design()
design.read_verilog("top.sv", systemverilog=True)
design.set_top("top")
design.elaborate()

for prop in design.properties:
    print(f"{prop.name}: {prop.expr}")          # pretty-printed
    print(f"  kind: {prop.expr.id}")            # e.g. "sva_always"
    print(f"  type: {prop.expr.type}")          # e.g. "bool"

    # Walk the expression tree
    for sub in prop.expr.depth_first():
        if sub.is_symbol:
            print(f"  references signal: {sub.identifier}")

    # Pattern: find all 'eventually' sub-properties
    for ev in prop.expr.find("sva_s_eventually"):
        print(f"  has liveness sub-property: {ev.property}")
```

### Filtering properties by expression structure

```python
# Find all properties that reference a specific signal
def properties_referencing(design, signal_name):
    for prop in design.properties:
        symbols = [s for s in prop.expr.find("symbol")]
        if any(signal_name in s.identifier for s in symbols):
            yield prop

# Find all liveness properties
liveness = [p for p in design.properties
            if p.expr.id in ("sva_s_eventually", "sva_eventually", "F")]
```

### Constructing expressions (future / advanced)

For advanced use cases (adding constraints, custom properties), expression
construction mirrors the tree structure:

```python
from pyebmc.cprover import symbol, constant, G
from pyebmc.cprover import unsigned_bv

# Build: G(counter != 0)
counter = symbol("main.counter", type=unsigned_bv(8))
zero = constant(0, type=unsigned_bv(8))
prop_expr = G(counter != zero)

design.add_property("my_prop", prop_expr)
```

This is a future extension; the initial release focuses on read-only
expression inspection.

---

### Implementation Notes for Expr/Type Bindings

The pybind11 layer wraps `exprt` and `typet` in a `cprover` submodule:

```cpp
// In _engine.cpp (pybind11 module)
auto cprover = m.def_submodule("cprover", "CBMC IR types");

py::class_<exprt>(cprover, "Expr")
    .def_property_readonly("id", [](const exprt &e) {
        return id2string(e.id());
    })
    .def_property_readonly("type", [](const exprt &e) {
        return e.type();
    })
    .def_property_readonly("operands", [](const exprt &e) {
        return py::tuple(py::cast(e.operands()));
    })
    .def("get", [](const exprt &e, const std::string &key) -> py::object {
        auto &val = e.find(dstringt(key));
        if(val.is_nil()) return py::none();
        return py::cast(id2string(val.id()));
    })
    .def("__str__", [](const exprt &e) {
        return format_to_string(e);
    })
    .def("__repr__", [](const exprt &e) {
        return "<cprover.Expr id='" + id2string(e.id()) + "' operands=" +
               std::to_string(e.operands().size()) + ">";
    })
    .def("__eq__", [](const exprt &a, const exprt &b) { return a == b; })
    .def("__hash__", [](const exprt &e) { return e.hash(); });
```

The Python-side `pyebmc/cprover/expr.py` module adds the subclass dispatch,
convenience methods, and iteration protocol on top of the raw pybind11
wrapper. A registry maps `id` strings to Python subclasses:

```python
# pyebmc/cprover/expr.py

_EXPR_REGISTRY: dict[str, type[Expr]] = {
    "symbol": SymbolExpr,
    "constant": ConstantExpr,
    "sva_always": SvaAlwaysExpr,
    "sva_s_eventually": SvaEventuallyExpr,
    "G": GExpr,
    "F": FExpr,
    "U": UExpr,
}

def _wrap_expr(raw: _engine.cprover.Expr) -> Expr:
    """Wrap a raw C++ Expr into the appropriate Python subclass."""
    cls = _EXPR_REGISTRY.get(raw.id, Expr)
    obj = cls.__new__(cls)
    obj._raw = raw
    return obj
```

---

## Implementation Strategy

### Binding Layer

Use **pybind11** to wrap the C++ EBMC internals. The `_engine` module
exposes a thin C++ class that holds:

- A `cmdlinet` (populated from Python keyword args)
- A `transition_systemt` (after elaboration)
- An `ebmc_propertiest` (after property extraction)
- A `message_handlert` (routing messages to Python logging)

The Python `Design` class wraps `_engine.Session` and translates between
Pythonic types and the C++ IR.

### Build System

- Use `scikit-build-core` or `meson-python` for the build.
- Link against the existing EBMC/CBMC static libraries.
- Distribute as a wheel with bundled solver libraries.

### Message Handling

EBMC messages route to Python's `logging` module:

```python
import logging
logging.getLogger("pyebmc").setLevel(logging.WARNING)
```

This replaces the Tcl pattern of `set_verbose` / `suppress_message`.

---

## Comparison with EDA Tcl Idioms

| Tcl (Cadence/Synopsys style) | pyebmc |
|-|-|
| `read_verilog top.sv` | `design.read_verilog("top.sv")` |
| `set_top top` | `design.set_top("top")` |
| `elaborate` | `design.elaborate()` |
| `check_property -bound 10` | `design.check_property(bound=10)` |
| `get_property_status p1` | `design.properties[0].status` |
| `report_property -format json` | `design.report_properties(format="json")` |
| `write_vcd -file out.vcd` | `design.write_vcd("out.vcd", prop_id)` |
| `get_modules` | `design.modules` |
| `set_engine ic3` | `design.check_property(engine="ic3")` |
| `foreach p [get_properties] {...}` | `for p in design.properties: ...` |

---

## Future Extensions

- **Waveform viewer integration**: Return traces as pandas DataFrames.
- **Async check**: `await design.check_property_async(...)` for long-running checks.
- **Netlist access**: Expose gate-level netlist for custom analysis.
- **Coverage**: `design.report_coverage()` after BMC runs.
- **TCL compatibility shim**: A `pyebmc.tcl` module providing flat functions
  (`read_verilog(...)`, `elaborate()`, etc.) operating on a global session,
  for engineers migrating from Tcl scripts with minimal rewriting.
