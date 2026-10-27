module main;

  // 1800-2017 11.4.11: conditional operator with real operands

  // folded during elaboration
  parameter real A = 1 ? 1.5 : 2.5;
  parameter real B = 0 ? 1.5 : 2.5;
  parameter real C = (A > 2.0) ? A : A + 1.0;

  p0: assert final (A == 1.5);
  p1: assert final (B == 2.5);
  p2: assert final (C == 2.5);

  // not folded during elaboration
  p3: assert final ((1 ? 1.5 : 2.5) == 1.5);

  // must fail
  p4: assert final (B == 1.5);

endmodule
