// The "let construct" was introduced by SystemVerilog 1800-2009.

module main;

  let some_let = 8'd123;
  p0: assert final (some_let == 123 && $bits(some_let) == 8);

  // May depend on state.
  wire some_wire;
  let some_let_eq_wire = some_wire;

  p1: assert final (some_let_eq_wire == some_wire);

endmodule
