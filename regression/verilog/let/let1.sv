// The "let construct" was introduced by SystemVerilog 1800-2009.

module main;

  let some_let = 8'd123;
  p0: assert property (some_let == 123 && $bits(some_let) == 8);

  // The standard doesn't say, but we allow these to be elaboration-time
  // constants.
  parameter some_parameter = some_let;

  p1: assert property (some_parameter == 123 && $bits(some_parameter) == 8);

  // May depend on state.
  wire some_wire;
  let some_let_eq_wire = some_wire;

  p2: assert property (some_let_eq_wire == some_wire);

endmodule
