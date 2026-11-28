# The VHDL front-end

This directory contains the VHDL front-end of EBMC. It reads a VHDL design
(IEEE 1076-2008, the RTL synthesis subset of IEEE 1076.6-2004), checks it,
and produces a transition system in the symbol table, which the EBMC
engines then verify. The entity given with `--top` is the design under
verification; its assertions become the properties.

## Pipeline

```
   design.vhd
       |
       v
 +--------------+   flex/bison, reentrant scanner
 |  scanner.l   |   (vhdl_parser.h, verilog/flex_interface.h)
 |  parser.y    |
 +--------------+
       |  parse tree: design units (vhdl_parse_tree.h) with the
       |  statements, expressions and type definitions of
       |  vhdl_expr.h and vhdl_types.h; names are unresolved
       v
 +------------------------+
 |  vhdl_typecheck*.cpp   |   scopes, names, VHDL typing rules
 +------------------------+
       |  symbol table: one symbol per port, signal and variable,
       |  the module symbol with the type-checked concurrent
       |  statements; all expressions have VHDL types
       v
 +------------------------+
 |  vhdl_synthesis.cpp    |   processes -> next-state functions,
 +------------------------+   concurrent statements -> constraints
       |  the module value is a transt: INIT, INVAR, TRANS;
       |  assertions are property symbols (still VHDL-typed)
       v
 +------------------------+
 |  vhdl_lowering.cpp     |   VHDL types and operators -> CBMC
 +------------------------+   types and operators, simplified
       |
       v
   symbol table with CBMC types ---> EBMC engines (BMC, k-induction,
                                     IC3, ...) and traces (expr2vhdl.cpp)
```

The driver is `vhdl_ebmc_language.cpp` (for `ebmc`) and `vhdl_language.cpp`
(the `languaget` interface). `--show-parse` prints the parse tree,
`--show-symbol-table` the result of type checking (with VHDL types),
`--show-trans` the lowered transition system.

## Parsing

`scanner.l` and `parser.y` are a flex scanner and a bison grammar for
IEEE 1076-2008. The scanner is reentrant and owned by `vhdl_parsert`
(`vhdl_parser.h`), which keeps the file, line and column through the
`YY_INPUT` and `YY_USER_ACTION` macros of `util/parser.h`; every token
and every parse tree node gets a source location. Basic identifiers are
case insensitive and are kept as written; the type checker lowers them.

The grammar covers the RTL synthesis subset of the language. Some
constructs cannot be told
apart syntactically and are disambiguated by the type checker:
`f(x)` is an indexed name, a slice, a function call or a type
conversion (`vhdl_indexed_exprt`), and `t'(e)` is a qualified
expression.

The parse tree (`vhdl_parse_tree.h`) is a list of design units: library
and use clauses, entities, architectures, packages. Their contents are
`exprt`/`typet` trees with the classes of `vhdl_expr.h` (statements,
derived from `vhdl_statementt`, and the VHDL-specific expressions) and
the type definitions at the end of `vhdl_types.h`. All VHDL-specific
irep ids are prefixed `vhdl_` and declared in `src/hw_cbmc_irep_ids.h`.

## Type checking

`vhdl_typecheckt` (`vhdl_typecheck_class.h`, implemented in
`vhdl_typecheck.cpp` for declarations and statements,
`vhdl_typecheck_expr.cpp` for expressions and `vhdl_typecheck_type.cpp`
for types) checks the entity and architecture of the top-level entity,
and the packages of the design file.

Scoping follows IEEE 1076-2008 12.3: each declarative region (the
predefined types, the packages, the entity, the architecture, each
process and block) is a map from lower-case names to declarations.
A declaration hides a homograph in an outer region, whatever its kind;
a second declaration in the same region is an error. Enumeration
literals may be overloaded; the type of an overloaded literal is
determined by the context. Statement labels are declarations.

Objects become symbols named `vhdl::<entity>.<name>`, and
`vhdl::<entity>.<process>.<name>` for process variables, which are
marked `is_auxiliary`. Constants are inlined, for loops with static
ranges are unrolled, and generics are constants with their default
value.

The result has **VHDL types** (the classes in the middle of
`vhdl_types.h`): `vhdl_enumeration_typet` (boolean, bit, std_ulogic,
character, user-defined enumerations), `vhdl_integer_typet` (always
with its range), `vhdl_array_typet` (element type, index subtype, and
the index range when constrained) and `vhdl_record_typet`. A type carries its name and the name of its base type; two
types are compatible when the base types agree, which gives VHDL's
strong typing: `bit` and `boolean`, or `std_logic_vector` and
`unsigned`, are distinct.

The expressions use the generic CBMC operators (`ID_plus`, `ID_equal`,
`ID_index`, `ID_concatenation`, ...) on VHDL-typed operands, with the
result types of IEEE 1076-2008 9.2 and of the numeric packages; the
exceptions are `vhdl_slice_exprt` for slices, and `ID_vhdl_event`,
`ID_vhdl_rising_edge` and `ID_vhdl_falling_edge` for the clock edges.
The type checker decides what is legal (same types and lengths for the
predefined operators, numeric_std operators only when the package is
used, static choices covering a case selector exactly once, ...), but
leaves the encoding to the lowering. Literals are universal until the
context gives them a type (`convert_to`).

## Synthesis

`vhdl_synthesist` (`vhdl_synthesis_class.h`, `vhdl_synthesis.cpp`)
turns the type-checked architecture into a transition system with one
implicit clock, following IEEE 1076.6-2004: clocked processes give
next-state functions (TRANS), the other processes and the concurrent
assignments give constraints (INVAR), initial values give INIT, and
assertions become property symbols. Everything stays VHDL-typed. The
synthesis is not part of this change; `vhdl_synthesis.cpp` rejects
every design until it lands.

## Lowering

`vhdl_lowering.cpp` maps the symbol table to CBMC types, after
synthesis: boolean, bit and std_(u)logic become `bool`, integer types
`signedbv(32)`, arrays of bits `unsignedbv`/`signedbv`, other arrays
`array`, enumerations `enumeration`, records `struct`. It implements
the VHDL operators on these: index positions (the left-most element is
the most significant bit, so `v(i)` of `v(7 downto 0)` is bit `i`),
lexicographic array comparisons, the widths and full-precision
comparisons of numeric_std, `mod` and `rem`, enumeration ordering,
and `update_bit` for partial assignments. The design is two-valued:
only `'0'` and `'1'` have a value in the lowered design. `'L'` and
`'H'` are accepted as the operand of the condition operator `??`, where
they read as false and true (IEEE 1076-2008 9.2.9), and are rejected
anywhere else, as are the other values of std_ulogic.

## Tests

* `regression/vhdl`: by topic (`operators`, `processes`, `concurrent`,
  `types`, `design-units`, `parser`, `typecheck_errors1`); each input
  has a `-parse`, a `-typecheck` and a BMC `.desc`.
* `unit/vhdl`: the parse tree, parser, expression and type classes,
  and the lowering.

## References

* IEEE 1076-2008, VHDL Language Reference Manual
* IEEE 1076.6-2004, VHDL Register Transfer Level (RTL) Synthesis
* IEEE 1076.3 (numeric_std), IEEE 1164 (std_logic_1164)
* A VHDL reference: http://edg.uchicago.edu/~tang/VHDLref.pdf
