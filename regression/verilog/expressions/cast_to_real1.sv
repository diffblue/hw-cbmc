module main;

  // no rounding
  p0: assert final (real'(0) == 0.0);
  p1: assert final (real'(1) == 1.0);

  // rounding, away from zero
  p2: assert final (real'('hffff_ffff_ffff_ffff) == real'('h1_0000_0000_0000_0000));
  p3: assert final (real'(-'sh0_ffff_ffff_ffff_ffff) == real'(-'sh1_0000_0000_0000_0000));

endmodule
