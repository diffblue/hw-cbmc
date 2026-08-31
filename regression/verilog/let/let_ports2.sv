// SystemVerilog let with multiple ports

module main;

  let add(a, b) = a + b;
  let mul(x, y) = x * y;

  p0: assert final (add(3, 4) == 7);
  p1: assert final (mul(3, 4) == 12);
  p2: assert final (add(mul(2, 3), 1) == 7);

endmodule
