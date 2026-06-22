Docker-Based Validation: fastppa vs Real Synthesis
===================================================

This report replaces guesswork with a reproducible measurement. `COMPARISON.md`
and `CALIBRATION.md` in this directory cite specific accuracy numbers against
Yosys and Synopsys PrimeTime, but no script, log, or artifact in this repo
produced them, and PrimeTime is commercial software not available in this
environment. Treat the numbers in those two files as unverified. This report
is a real, reproducible run, and the cost model itself has since been fixed
based on what it found.

**Redo (2026-06-22):** the comparison was rerun end-to-end after fix #7 below
(struct/array operand width). Two corrections to the run itself, not the
cost model: (a) `divider`, `parity`, `comb_mux` and `large_array` already
existed in `regression/fastppa/{blocks,designs}` but were missing from the
original table despite the Method section's "no designs cherry-picked"
claim — they are now included; (b) `struct_mux` (a struct-typed mux,
`regression/fastppa/blocks/struct_mux.sv`) was added specifically to exercise
fix #7. All numbers below are from this rerun (26 designs + the Rocket core),
not the original run.

**Second redo (2026-06-22, same day):** `regfile`'s delay gap (0.21×, left
open by the first redo) was investigated and root-caused, producing fixes
#9 and #10 below (`index_cost` recalibration, and a separate constant-index
bug found along the way). The results table, the Rocket-core table, and the
`large_array` note are updated in place to reflect fixes #9/#10 on top of
fix #7 — they are not yet a separate fix-#7-only column except where called
out explicitly (the summary-statistics table keeps both).

Method
------

- Tool image: `openroad/orfs:latest` (run with `--platform linux/amd64`,
  emulated — no native arm64 build exists), pulled fresh, used purely for
  isolation/reproducibility, not modified.
- Synthesis: Yosys 0.64 + ABC, `synth -top <top> -flatten`, mapped with
  `dfflibmap` + `abc -liberty` to the **NanGate45 typical** liberty shipped in
  that image (`flow/platforms/nangate45/lib/NangateOpenCellLibrary_typical.lib`,
  from OpenROAD-flow-scripts). Area read from `stat -liberty` ("Chip area for
  module").
- Timing: standalone `sta` binary (OpenSTA, bundled in the same image) on the
  synthesized netlist, same liberty, a virtual `create_clock -period 50`
  (loose enough to not bind) attached to the design's actual clock port,
  zero input/output delays, `report_checks -path_delay max`. Delay = "data
  arrival time" of the worst path — the real reg-to-reg (or port-to-reg)
  critical path, the same quantity fastppa reports as "Reg-to-reg delay".
  Gotcha hit during the redo: the clock port isn't always named `clk` (the
  Rocket core's is `clock`) — get this wrong and OpenSTA silently reports
  only stray port-to-port combinational paths instead of an error, giving a
  plausible-looking but far too short delay. Verify the chosen clock port
  actually exists before trusting a `sta` delay number.
- fastppa: built locally at this commit, run as
  `fastppa <file> --top <top> --process 45nm`, the 26 designs in
  `regression/fastppa/{blocks,designs}` (`counter` excluded, see below),
  plus the per-operator, multi-width benchmarks in
  `benchmarking/fastppa_scaling/{adder,mult,shift,cmp}_{8,16,32,64,128}.sv`
  and `{div,mod}_{8,16,32,64}.sv` used for the per-operator calibration below.
- fastppa timed with shell `time` around the whole invocation; Yosys and
  OpenSTA timed separately (each prints its own elapsed time) so the two
  steps can be told apart.

Fixes applied (root-caused from this data)
-------------------------------------------

1. **FSM/case select logic was entirely uncosted.** `walk_fsm_branches`
   walked branch *values* but never the branch *conditions* or the
   resulting mux — a literal 4-way `case` mux (`mux_tree`) cost 0 ps / 0 µm²
   of decode logic. Fixed by costing each condition and adding a mux-select
   cost; a global cache means a shared FSM state decode (the same
   `state == X` driving many registers, as in `fp_adder`) is only paid for
   once, not once per register.
2. **Register area was 10.0 µm²/bit; real NanGate45 `DFF_X1` is 4.52 µm²/bit**
   — read directly off synthesized cell stats (`32 144.704 DFF_X1` etc.),
   consistent to 3 significant figures across every design checked.
3. **SRAM-density costing kicked in at 64 bits.** A 32×32 (1024-bit)
   register file (`regfile`) was costed at SRAM density (1 µm²/bit) when
   real synthesis just used 1088 ordinary flip-flops (`regfile`'s real DFF
   count matches fastppa's register-bit count almost exactly). Raised the
   threshold to 4096 bits — small-to-medium register files realistically
   synthesize as flip-flops, not SRAM macros.
4. **Per-operator area/delay formulas were recalibrated** against real
   multi-width synthesis data (comb-only area, after subtracting measured
   DFF area):
   - `+`/`-`: delay turned out **linear** in width (~34 ps/bit), not
     logarithmic (`50 + 30*log2(n)` underestimated a 32-bit adder's real
     1.11 ns critical path by 5.5×).
   - `*`: delay sub-linear, `~71 * n^0.86` ps; area `~1.6 * n²` µm²
     (down from `2.5 * n²`, which over-estimated by ~1.5×).
   - shift: delay has both a log-depth term and a width/fanout term,
     `54*log2(n) + 1.3*n` ps; area `~2.51 * n^1.32` µm².
   - comparator: delay `67.5*log2(n)` ps (was `40 + 25*log2(n)`, ~2× low);
     area `3.8` µm²/bit (was `3.0`).
   - `div`/`mod` were not recalibrated — no divider in the calibration set,
     treat with more caution than the other arithmetic operators.
5. **FSM resource-sharing discount.** Iterative FSM-based datapaths
   (`fp_adder`, `fp_divider`, `fp_multiplier`, `float_to_int`,
   `int_to_float`) reuse the same functional units across many states and
   registers — real Yosys `share`-style optimization collapses this, which
   a per-register DAG walk can't see. The RTL's own "activity ratio" (how
   sparse per-state register updates are) correlated cleanly with the
   over-estimation actually measured (activity ratios of 0.28–0.46 needed
   roughly the square of that ratio applied to combinational area), so a
   `activity_ratio²` area discount is applied when activity ratio < 1.
6. **Associative-chain delay was not balanced.** A literal sum-of-products
   `((a*c0 + b*c1) + c*c2) + d*c3` (as written in `fir4`/`fir16`) was
   costed as 3 literal addition stages; real synthesis restructures
   associative `+`/`-`/`&`/`|`/`^` chains into a balanced tree
   (4 terms → `log2(4) = 2` stages), which is now modeled.
7. **(2026-06-22 redo) Struct/array operand width was silently 1.** `get_width()`
   in `estimate.cpp` only recognized `ID_bool` and `bitvector_typet`; any
   struct, array, or packed-union-typed operand or register (a struct-typed
   register, a struct-typed mux, an array used directly as a mux/comparison
   operand) fell back to width 1, undercounting its area, delay, and energy
   by however many bits it actually was. Confirmed directly: `regfile`'s
   8-register-array decode/mux logic and `large_array`'s 256-entry array
   write/read decode were costed as if 1 bit wide. Fixed by calling the
   codebase's existing `verilog_bits_opt()` (`src/verilog/verilog_bits.h`,
   already used by the Verilog frontend itself) instead of reimplementing
   width computation by hand — this also gets packed unions right (width =
   max member, not sum) for free, which the old code never attempted at all.
8. **(2026-06-22) `div`/`mod` calibrated.** The redo's `divider` measurement
   (27.66 ns real critical path vs fastppa's 3.45 ns, 8× low) showed the
   previous linear guess (`200 + 100*n` ps delay, `8*n` area_per_bit) was
   never calibrated at all — there was no divider in the original
   calibration set. Added `benchmarking/fastppa_scaling/{div,mod}_{8,16,32,64}.sv`
   (single-operator, isolated from each other unlike `divider.sv` which has
   both) and fit power laws to real Yosys+ABC+OpenSTA data: area
   `4.34 * n^1.98` µm² (essentially quadratic, as expected for an unrolled
   subtract-compare-shift array) and delay `38.3 * n^1.89` ps (also close to
   quadratic, not the old linear-in-n guess) — within ~6% of measured at
   every width 8–64. `div` and `mod` were measured separately and converge
   to within ~2% of each other by n=64 (real synthesis shares the
   subtract/compare/shift array between quotient and remainder), so one
   shared formula is fit to both, matching the existing code structure.
9. **(2026-06-22) `index_cost` (array read decode) recalibrated for both
   delay and area.** Root-caused from `regfile`'s known delay gap (0.21×,
   left open by fix #7): the old formula (`25*levels` ps, `3.0*n*levels`
   µm², `levels = ceil(log2(array_size))`) modeled only the decode tree's
   *depth*, which matches real synthesis almost exactly as a level count,
   but missed that the address bits driving the decode fan out to
   `~array_size` places — at `array_size >= 16` real synthesis inserts a
   buffering stage whose own delay (driven by that fan-out) dominates the
   path. Confirmed directly: a 32-entry read's real critical path is
   0.97 ns vs the old model's 125 ps. Added
   `benchmarking/fastppa_scaling/regfile_{4,8,16,32,64}.sv` and used
   `report_checks -from [get_ports raddr]` (the write port can otherwise
   dominate the *global* critical path at small array sizes, hiding the
   read path) to isolate the read-port delay cleanly across array sizes
   4–64. New delay formula: `27.1*levels + 25.8*array_size` ps. Area was
   calibrated separately, against
   `benchmarking/fastppa_scaling/idx_{4,8,16,32,64}.sv` — a register array
   with an independent per-entry write enable (no address-decoded write),
   which isolates the read decode/mux tree's area without the write
   port's own decode logic mixed in (three earlier attempts at an
   isolated read-only design were defeated by Yosys's optimizer: an
   undriven array gets eliminated entirely, and a uniformly- or
   algebraically-driven one gets collapsed by constant/equivalence
   propagation before the read mux is ever built). New area formula:
   linear in `array_size`, not log — `n * (2.82*array_size + 5.12)` µm²
   (real decode/mux-tree gate count grows linearly with the number of
   array elements, not with the tree depth). Effect: `regfile`'s delay
   ratio went from 0.21× to **1.21×**; `large_array`'s delay went from
   0.03× (33× low) to **0.92×**, and its area from 0.68× to **1.02×**
   (though see the new `large_array` note below — that area match is
   partly coincidental).
10. **(2026-06-22) Constant array indices were costed as if they needed a
    full decoder.** `cost_operator`'s `ID_index` branch called
    `index_cost()` unconditionally, without checking whether the index
    operand was actually a runtime signal. A *constant* index
    (`mem[3]`, or `mem[i]` after a bounded `for`-loop is unrolled, as in
    `array_sorter`'s min/max scan) selects a fixed element at synthesis
    time — it's direct wiring to that element's bits, not a mux tree — so
    real synthesis charges it nothing. Found while investigating why fix
    #9's index_cost recalibration made `array_sorter` *worse* (1984.1 µm²
    → 2581.8 µm²): its 8-iteration unrolled scan over `mem[i]` was
    generating 8 separate full-price decoder costs for indices that are
    each a single literal once unrolled. Fixed by checking the index
    operand against the same `resolve_to_constant` helper already used
    for the constant-operand discount on `*` (so it also catches indices
    resolved through invariant/constant propagation, not just literal
    `ID_constant` nodes), and returning zero cost when it resolves.
    Regression test: `regression/fastppa/blocks/const_index.sv`. Net
    effect on `array_sorter` (combining fixes #9 and #10): 1984.1 µm² →
    1704.2 µm² — an improvement over the pre-#9 baseline, not just a
    reversion.

Known limitations found but not fixed:
- When several comparisons share the same operand pair (e.g.
  `lt<=a<b; eq<=a==b; gt<=a>b`), real synthesis often derives all three from
  one subtraction and shares the hardware; fastppa still costs each
  comparison independently (confirmed on the `cmp_*` calibration benchmarks,
  ~2.2–3.0× over-estimate there, unchanged by fix #7 since it's unrelated to
  width). Tracked as `regression/fastppa/bugs/shared_comparator_bug.45nm.desc`
  (`KNOWNBUG`).
- Fix #8 calibrated `div`/`mod` in isolation but exposed the same class of
  gap one level up: `divider.sv` computes both `q<=a/b` and `r<=a%b` from
  the same operands, which real synthesis derives from one shared
  subtract/compare/shift array (confirmed: the combined module's real area,
  4325.2 µm², is close to *one* divider's area, not two) — but fastppa has
  no operand-pair CSE across arithmetic ops (the same root cause as the
  comparator-sharing limitation above, just for `/`/`%` instead of
  `<`/`==`/`>`), so it costs `div` and `mod` as two independent dividers
  (now 9177.6 µm², 2.12× over, vs the pre-calibration 16673.3 µm², 3.85×
  over — still wrong, but for a single, understood reason instead of an
  uncalibrated formula). Delay is no longer affected by this (only one of
  the two shares the critical path), and is now accurate: 26.84 ns vs
  27.66 ns real (0.97×, was 0.12×).
- Fix #9 fixed `regfile`'s long-standing *delay* gap (0.21× → 1.21×) but
  moved its *area* the other way (1.01× → 1.52×), and similarly worsened
  `riscv_pipe` (1.21× → 1.69×) and only partially improved `array_sorter`
  (1.74× → 1.50×, after fix #10 also strips its constant-index reads).
  Root cause, confirmed by an ablation on `large_array` (drop the write
  port, keep only `rdata <= mem[raddr]`): the *read* side, costed via
  fix #9's new `index_cost`, tracks real comb area closely on its own
  (23 265 µm² fastppa vs an estimated 29 472 µm² real comb-only at
  256 entries — reasonable, given fix #9 was calibrated up to 64). The
  *write* side (`mem[waddr] <= wdata`, modeled as an `ID_with` array
  update) isn't costed by `index_cost` at all — `walk_expr` has no
  `ID_with` case, so it falls through to `cost_operator`'s generic
  "simple logic" default bucket (`2.0` µm²/bit), applied to the *entire
  array's* aggregate width (8192 bits for `large_array`, not the
  32-bit element actually written) — and contributes 36 045 µm² on its
  own, more than the read side, with no real decoder of comparable size
  behind it. `regfile` and `riscv_pipe` have *two* runtime-indexed reads
  plus this same uncosted-shaped write, so the now-larger read-side
  `index_cost` numbers no longer have an over-counted write side to
  (coincidentally) net out against the way they used to pre-fix-#9. Not
  fixed here: doing so means giving `ID_with` its own decoder-shaped cost
  function (structurally an array-write analogue of `index_cost`, scaled
  by the *element* width like a write-enable decoder, not the whole
  array), calibrated against its own isolated data — out of scope for
  this round, which was about `regfile`'s delay gap specifically.
- Checked whether `mux_cost` (FSM/case select logic, fix #1) needed the
  same depth-only-misses-fan-out correction as fix #9. It doesn't, for a
  structural reason: `walk_fsm_branches` combines branch conditions via
  `max` (parallel evaluation), not a sum, and real FSM/case state counts
  are small enough in practice that the existing model tracks real
  synthesis closely through 8-way selects (ratio 0.99–1.03 on an
  isolated 4/8-way case-mux benchmark) and only degrades mildly by
  16–32 way (0.86×, 0.77×) — nowhere near `index_cost`'s old 8× gap,
  and well beyond what a typical FSM's state count looks like. Found
  along the way, but not fixed (out of scope here, and orthogonal to
  mux_cost itself): a case statement with branch labels written as
  *unsized* integer literals (`0`, `1`, ... instead of `2'd0`, `2'd1`,
  ...) gets each branch condition's comparator costed at the
  implicitly-widened 32-bit comparison width Verilog gives it, instead
  of the width that actually matters once the constant's always-zero
  upper bits are accounted for — a 6× area inflation observed on an
  isolated benchmark. None of the existing FSM-pattern regression
  designs hit this (they all use explicitly-sized literals, like
  `mux.sv`'s `2'b00`), so it doesn't affect any number in the table
  below, but a case statement written with bare integer literals
  elsewhere would silently over-cost.
- Fix #7 exposed, rather than fixed, a separate gap in `struct_packet`: its
  area ratio moved from 0.69× (under, while the width bug was active) to
  2.25× (over, now that it's fixed) — a sign flip, not an improvement. Cause:
  `struct_packet` declares a `pkt_in` struct purely as a same-cycle scratch
  value (written and fully consumed within one `always` block, never read
  across a clock edge); real synthesis proves it dead and allocates no
  flip-flops for it (190 actual `DFF_X1`, not the 257 bits the source
  declares), while fastppa still charges full register cost for every
  declared state variable. This is the same class of blind spot already
  documented below for `counter` (no liveness/dead-register analysis), now
  visible on a second design because fix #7 stopped a struct-width bug from
  accidentally compensating for it.
- `large_array` (8224 register bits): before fix #9, fastppa under-estimated
  area 0.68× and delay 0.03× (~29× low) relative to Yosys+ABC. Fix #9
  closed delay to 0.92× and, on the surface, area to 1.02× — but the area
  match is a coincidence, not validated accuracy, and the underlying
  methodology caveat from the original run still applies: this open-source
  flow has no SRAM compiler in the loop, so Yosys just unrolls the
  256-entry `reg [31:0] mem[0:255]` into 8224 plain flip-flops (confirmed:
  8224 `DFF_X1`, ~37 200 µm² for registers alone), while fastppa's
  >4096-bit SRAM-density model (1 µm²/bit) charges only 8336.6 µm² for the
  same 8224 bits — under-counting registers by ~4.5×. What changed is that
  fix #9 also pushed *comb* area up to 59 310 µm² against an estimated
  real comb-only of ~29 472 µm² (register area subtracted from the real
  total) — over-counting comb by ~2× (see the new `regfile`/`riscv_pipe`
  area note above; same root cause, the uncosted-shaped `ID_with` write
  path). The register under-count and the comb over-count happen to
  net out to a good *total* at this specific size; neither component is
  individually accurate, and the SRAM-vs-flip-flop register methodology
  gap means this design still isn't a like-for-like comparison. Don't use
  this design's total ratio to judge or recalibrate either the SRAM
  threshold or `index_cost`.

Results after the 2026-06-22 redo (fix #7 + expanded design set)
------------------------------------------------------------------

| design | real area (µm²) | fastppa area | area ratio | real delay (ns) | fastppa delay | delay ratio |
|---|---|---|---|---|---|---|
| adder | 324.0 | 336.6 | 1.04 | 1.112 | 1.138 | 1.02 |
| aes_round | 1817.3 | 2286.0 | 1.26 | 0.356 | 0.198 | 0.56 |
| alu | 1217.2 | 885.1 | 0.73 | 1.482 | 1.240 | 0.84 |
| array_sorter | 1138.7 | 1704.2 | 1.50 | 2.317 | 1.701 | 0.73 |
| bf16_fma | 983.4 | 1155.4 | 1.17 | 2.069 | 3.510 | 1.70 |
| comb_mux | 44.7 | 50.4 | 1.13 | 0.105 | 0.100 | 0.95 |
| divider §| 4325.2 | 9177.6 | 2.12 | 27.657 | 26.839 | 0.97 |
| fir16 | 6379.5 | 6069.8 | 0.95 | 2.011 | 4.619 | 2.30 |
| fir4 | 1299.7 | 1481.6 | 1.14 | 1.347 | 2.428 | 1.80 |
| float_to_int | 1174.9 | 1398.3 | 1.19 | 1.448 | 1.306 | 0.90 |
| fp_adder | 2948.1 | 3920.7 | 1.33 | 1.177 | 2.427 | 2.06 |
| fp_divider | 3404.0 | 4213.7 | 1.24 | 2.128 | 2.390 | 1.12 |
| fp_multiplier | 6340.1 | 3461.2 | 0.55 | 2.189 | 2.428 | 1.11 |
| fsm_datapath | 317.3 | 329.0 | 1.04 | 0.889 | 0.670 | 0.75 |
| fsm_shared_mult | 3867.1 | 2042.8 | 0.53 | 1.455 | 2.589 | 1.78 |
| int_to_float | 1480.3 | 1549.6 | 1.05 | 1.388 | 1.415 | 1.02 |
| large_array †† | 66644.4 | 67646.7 | 1.02 | 7.446 | 6.878 | 0.92 |
| multiplier | 1775.8 | 1783.0 | 1.00 | 1.468 | 1.449 | 0.99 |
| mux | 77.4 | 123.4 | 1.59 | 0.139 | 0.193 | 1.39 |
| parity | 54.0 | 36.5 | 0.68 | 0.215 | 0.100 | 0.46 |
| pipe_mult | 2065.2 | 2072.3 | 1.00 | 1.636 | 1.449 | 0.89 |
| regfile | 10238.1 | 15526.4 | 1.52 | 0.836 | 1.015 | 1.21 |
| riscv_pipe | 10684.7 | 18052.2 | 1.69 | 2.343 | 1.249 | 0.53 |
| shifter | 415.0 | 388.1 | 0.94 | 0.293 | 0.362 | 1.23 |
| struct_mux ‡ | 987.4 | 1642.2 | 1.66 | 0.132 | 0.117 | 0.89 |
| struct_packet | 884.7 | 1991.2 | 2.25 | 0.135 | 0.175 | 1.29 |

†† see the `large_array` note above — area match is coincidental, register
   under-count and comb over-count netting out; not a like-for-like
   comparison either way.
‡ new design added in this redo specifically to exercise fix #7.
§ post fix #8 (div/mod calibration); area ratio reflects the div+mod
  hardware-sharing gap noted above, not a calibration error — see the
  isolated `div_32`/`mod_32` calibration data in the fix #8 description
  for the per-operator numbers without that confound.

| metric | original run (21, before fix #7) | redo, same 21 (fix #7) | redo, full 26 (fix #7) | full 26 (fixes #9, #10) |
|---|---|---|---|---|
| Area ratio | 1.04 / 0.97 / 0.53–1.59 | 1.05 / 1.08 / 0.53–2.25 | 1.09 / 1.09 / 0.53–2.25 | 1.13 / 1.13 / 0.53–2.25 |
| Delay ratio | 1.02 / 1.03 / 0.21–2.30 | 1.02 / 1.03 / 0.21–2.30 | 0.98 / 0.87 / 0.03–2.30 | 1.00 / 1.05 / 0.47–2.30 |

(median / geomean / range, ratio = fastppa / real)

Reading this: on the original 21-design set, fix #7 leaves the *median*
essentially unchanged (it was never about that set's typical case) but
widens the *range* — it trades `regfile`'s area error (0.57× → 1.01×, now
one of the best-fitting designs) for a new one on `struct_packet` (0.69× →
2.25×, see the liveness-gap note above) of similar magnitude in the other
direction. Net: fix #7 is still correct (it fixes a real, confirmed bug —
struct/array types were costed as 1 bit regardless of actual width), but it
is not, by itself, a net accuracy win on this particular sample; the
`struct_packet` finding above is the next thing to fix if accuracy on
struct-heavy designs matters. The 5 newly-added designs (`divider`,
`parity`, `comb_mux`, `large_array`, `struct_mux`) pull the full-26-design
area range wider still — now mostly the SRAM-methodology caveat on
`large_array` (`divider`'s area gap shrank from 3.85× to 2.12× once fix #8
calibrated `div`/`mod`, and its delay gap closed almost entirely, 0.12× →
0.97×). Neither remaining outlier is caused by fix #7.

Fixes #9/#10 are a clear *delay* win and a mixed *area* result. Delay: the
worst-case ratio across all 26 designs improves from 0.03× (`large_array`,
33× low) to 0.47× (`parity`, an unrelated and pre-existing gap) — the
specific, severe gap these fixes targeted is gone, and the median/geomean
both land almost exactly at 1.00/1.05. Area: the median/geomean tick up
slightly (1.09 → 1.13) because the now-correctly-calibrated `index_cost`
makes `regfile`, `riscv_pipe`, and (before fix #10) `array_sorter` worse,
not better — fix #9 was right about the read side (confirmed via the
`large_array` read-only ablation above) but it had been getting too much
credit from a coincidentally-cancelling write-side bug (the uncosted-shaped
`ID_with` default-bucket path, see the new known-limitation note above).
Net assessment: ship the delay fix, treat the area regression on
write-heavy array designs as the next thing to fix, same way `struct_packet`
was flagged after fix #7.

`counter` still excluded: it has no observable output, so real synthesis
dead-code-eliminates the entire design, while fastppa still charges full
register + increment-adder cost. fastppa does not do liveness analysis;
this is a genuine, structural blind spot, not a numeric error, and is not
addressed by any fix above — and is now also visible on `struct_packet`
(see above).

Speed (measured directly, wall-clock, this redo): `adder` — fastppa 0.005s vs
Yosys+ABC+OpenSTA 1.42s (~280×); `regfile` — fastppa 0.005s vs 12.76s
(~2550×, dominated by ABC mapping 1088 flops + decode logic); `Rocket` —
fastppa 0.093s vs 3.32s (~36×, the smallest margin of the three, since
Rocket is the one design here large enough that fastppa's own DAG walk cost
starts to show). Real range is ~36×–2550× depending on design size and
shape, not a flat number — unaffected by the accuracy fixes, since they
only changed cost constants, not algorithmic complexity.

Real-world validation: Rocket core (commercial PrimeTime ground truth)
------------------------------------------------------------------------

All of the above is calibrated against open-source synthesis (Yosys+ABC) as
a proxy for "real" PPA. To check that proxy against an actual commercial
flow, the same RTL and a genuine PrimeTime report were pulled from
[RTL-Timer](https://github.com/hkust-zhiyao/RTL-Timer) (BSD-3-Clause):
`Rocket` core module (RV32 in-order pipeline core, 2829 lines, 8
submodules: `RVCExpander`, `IBuf`, `CSRFile`, `BreakpointUnit`, `ALU`,
`MulDiv`, `PlusArgTimeout`, `Rocket` itself) from the TinyRocket chipyard
config, with a real `Information: Checked out license 'PrimeTime-ADV'`
post-route report at NanGate45 (`report_example/rpt_data/net/
Rocket_TinyRocket_route_TYP_SAIF_SDF/Rocket.qor.rpt` and
`Rocket.total_area.rpt`).

| | Area (µm²) | ratio vs PT | Delay (ns) | ratio vs PT | wall time |
|---|---|---|---|---|---|
| PrimeTime (real, post-route) | 42015.0 | 1.00 | 2.989 (39 levels of logic) | 1.00 | (commercial RTL-to-GDS flow) |
| Yosys+ABC+OpenSTA (open-source, single-pass) | 26119.1 | 0.62 | 5.300 | 1.77 | 3.3 s |
| fastppa (original run) | 47572.2 | 1.13 | 5.825 | 1.95 | 0.1 s |
| fastppa (this redo, post fix #7) | 51537.0 | 1.23 | 5.825 | 1.95 | 0.09 s |
| fastppa (post fixes #9, #10) | 56499.5 | **1.35** | 5.825 | **1.95** | 0.09 s |

(Yosys+ABC+OpenSTA wall time re-measured at 3.3s, not the original report's
13.4s — same container, same steps, just measured per-step this time
instead of including per-invocation container startup; not a methodology
change, just a more precise measurement.)

Three things stand out:

- **Area moved from 1.13× to 1.23×** after fix #7 — Rocket's RTL has
  several array/struct-typed structures (e.g. its CSR file, register file)
  that were previously costed at the old, too-low width, so this is the
  expected direction. It's still close to commercial PPA, and notably
  closer than it is to its own open-source proxy (Yosys+ABC under-shoots at
  0.62×, since Yosys's generic mapping is less area-efficient than
  commercial DC/ICC on a design this size).
- **Area moved again, 1.23× to 1.35×, after fixes #9/#10** — net effect of
  recalibrating `index_cost` upward for Rocket's register file/CSR-file
  reads (fix #9), partially offset by zeroing out whatever constant-index
  accesses fix #10 caught. Consistent with the same-direction area
  regression seen on `regfile`/`riscv_pipe` in the table above, and the
  same likely cause (the array-write `ID_with` path, not recalibrated
  here, no longer being coincidentally offset by an under-counted read
  side).
- **Delay is unchanged (5.825 ns, ratio 1.95 vs PrimeTime) across fix #7
  and fixes #9/#10** — Rocket's modeled critical path apparently doesn't
  run through an array read at all (plausible: at 180 levels of logic,
  dominated by the ALU/MulDiv combinational chains rather than a
  register-file read early in the pipeline), so neither the width fix nor
  the index_cost recalibration touched it. It still tracks the open-source
  single-pass baseline (5.300 ns, Yosys+ABC+OpenSTA) closely (ratio 1.10
  vs that baseline). The ~2× gap to PrimeTime is mostly a
  single-pass-synthesis vs. timing-closed-physical-design gap, not
  specific to fastppa: a real RTL-to-GDS flow runs register retiming,
  gate sizing, buffer insertion and iterative ECOs to close timing, none
  of which a single logic-synthesis pass (Yosys+ABC) or a word-level cost
  model (fastppa) can replicate. This effect is invisible on the small
  calibration designs above (shallow enough that single-pass synthesis is
  already near-optimal) and only shows up on a deep, 39-level real core.
  Net: treat fastppa's delay number
  as "single-pass synthesis-grade", not "post-timing-closure-grade" — the
  gap to a fully optimized commercial flow grows with design depth.

Reproduction
------------

```
docker pull --platform linux/amd64 openroad/orfs:latest
# put every regression/fastppa/{blocks,designs}/*.sv (except counter.sv),
# benchmarking/fastppa_scaling/*.sv, and benchmarking/rocket_core/rocket_full.v
# into a work dir as <label>.sv, plus a manifest.txt of "<label> <relpath> <top>"
# lines, then:
docker run --rm --platform linux/amd64 -v "$PWD/work":/work -w /work \
  openroad/orfs:latest bash run_compare.sh
```

`run_compare.sh` (per manifest line): `yosys -p` a generated script doing
`read_verilog -sv -> hierarchy -check -top -> synth -flatten -> dfflibmap ->
abc -liberty -> clean -> write_verilog -> stat -liberty`, then `sta -no_init
-exit` on the synthesized netlist with the script described under Method
above — including the `[catch {create_clock ... [get_ports clk]}]` fallback
for designs whose clock port isn't named `clk` (or, like `comb_mux`, has no
clock at all). Area parsed from `grep "Chip area for module"`; delay from
the *first* `data arrival time` line in the `sta` log (`report_checks`
prints the same number again, negated, in its summary section — `tail -1`
on that grep gets the wrong sign and, on a design with no genuine paths,
the wrong number entirely; use `head -1`). The same flow was run on
`benchmarking/fastppa_scaling/*.sv` to get per-operator, multi-width
calibration points for fix #4 (`{adder,mult,shift,cmp}_*`), fix #8
(`{div,mod}_*`), and fix #9 (`regfile_{4,8,16,32,64}.sv` for delay, isolated
via `report_checks -from [get_ports raddr]`; `idx_{4,8,16,32,64}.sv` for
area, using a per-entry write-enable to avoid the write port's own decode
logic) — and on `benchmarking/rocket_core/rocket_full.v` (`--top Rocket`)
for the real-world PrimeTime comparison above — see
`benchmarking/rocket_core/README.md` for provenance.
