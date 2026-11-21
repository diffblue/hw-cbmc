module main;

  // When one operand is real and the other is shortreal, the shortreal
  // operand is cast to real, and the result is real (1800-2017 11.3.1,
  // 11.4.11), regardless of the order of the operands.

  shortreal sr = 1.0;
  real r = 1.0e-10;
  int i = 3;
  bit c = 0;

  p0: assert final ($typename(c ? r : sr) == "real");
  p1: assert final ($typename(c ? sr : r) == "real");
  p2: assert final ($typename(sr + r) == "real");
  p3: assert final ($typename(r + sr) == "real");

  // with real precision, 1.0 + 1.0e-10 is greater than 1.0
  p4: assert final (sr + r > 1.0);
  p5: assert final (r + sr > 1.0);

  // 1.0e-10 is not a shortreal value
  real x;
  assign x = c ? sr : r;
  p6: assert final (x == 1.0e-10);

  // shortreal and an integral operand yield shortreal
  p7: assert final ($typename(c ? sr : i) == "shortreal");
  p8: assert final ($typename(c ? i : sr) == "shortreal");

endmodule
