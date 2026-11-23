module main;

  bit [3:0] a = 4'b1100, b = 4'b1010;
  bit signed [3:0] s = -2, t = -1;

  // 1800-2017 11.4.11: a condition with a known 1 bit is true,
  // even when it has x/z bits
  p0: assert final ((2'b1x ? a : b) === a);
  p1: assert final ((2'bz1 ? a : b) === a);

  // A condition without a known 1 bit, but with x/z bits, is ambiguous.
  // The operands are combined bit-wise (Table 11-20).
  p2: assert final ((2'b0x ? a : b) === 4'b1xx0);
  p3: assert final ((1'bz ? a : b) === 4'b1xx0);
  p4: assert final ((1'bx ? a : a) === a);
  p5: assert final ((1'bx ? s : t) === 4'b111x);

  // x/z in the operands; z combined with z yields x
  p6: assert final ((1'bx ? 4'b1z0x : 4'b1z0x) === 4'b1x0x);
  p7: assert final ((1'b1 ? 4'b1z0x : a) === 4'b1z0x);

  // the same at elaboration time
  localparam logic [3:0] P = 1'bx ? 4'b1100 : 4'b1010;
  localparam logic [3:0] Q = 2'b1x ? 4'b1100 : 4'b1010;
  p8: assert final (P === 4'b1xx0);
  p9: assert final (Q === 4'b1100);

endmodule
