// The "let construct" was introduced by SystemVerilog 1800-2009.

module main;

  let some_let_with_port(x) = x + 1;
  p0: assert final (some_let_with_port(1) == 2);

endmodule
