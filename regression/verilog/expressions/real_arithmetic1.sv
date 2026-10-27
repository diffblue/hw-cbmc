module main;

  // 1800-2017 6.12: the real types are IEEE 754 floating-point.
  // Arithmetic rounds to nearest, ties to even, the IEEE 754 default.

  // folded during elaboration
  parameter real A = 1.5 + 1.0;
  parameter real B = 1.5 - 2.0;
  parameter real C = 1.5 * 2.0;
  parameter real D = 1.5 / 2.0;
  parameter real E = 1.5 + 2.0 * 3.0;
  parameter real F = 1.5 + 1;          // 1 is converted to real
  parameter real G = A + 1.0;          // uses another parameter
  parameter real H = 0.1 + 0.2;        // rounded
  parameter real I = 1.0 / 3.0;        // rounded

  p0: assert final (A == 2.5);
  p1: assert final (B == -0.5);
  p2: assert final (C == 3.0);
  p3: assert final (D == 0.75);
  p4: assert final (E == 7.5);
  p5: assert final (F == 2.5);
  p6: assert final (G == 3.5);
  p7: assert final (H != 0.3 && H > 0.3);
  p8: assert final (I * 3.0 == 1.0);

  // not folded during elaboration
  p9: assert final (1.5 + 1.0 == 2.5);
  p10: assert final (1.5 * 2.0 - 0.5 / 0.25 == 1.0);

  // must fail
  p11: assert final (A == 2.0);

endmodule
