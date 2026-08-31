// A module-level 'integer' loop counter shared by two combinational
// always blocks must not be reported as a driver conflict: integers are
// elaboration-only scratch and are turned into wires, not state.
// Regression for LogikBench basic/crossbar (and the koios circuits),
// which previously failed with "conflict with previous assignment".
module main(input [3:0] din, output reg [3:0] a, output reg [3:0] b);
  integer i;
  always @(*)
    for (i = 0; i < 4; i = i + 1)
      a[i] = din[i];
  always @(*)
    for (i = 0; i < 4; i = i + 1)
      b[i] = din[i];
  p0: assert final (a == b);
endmodule
