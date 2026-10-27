// A real used as a condition is true when it is nonzero
// (IEEE 1800-2017 11.4.7, 11.4.11, 12.4).
module main(input int i);
  // constants
  p0: assert final ((0.0 ? 1 : 0) == 0);
  p1: assert final ((3.0 ? 1 : 0) == 1);
  p2: assert final ((0.25 ? 1 : 0) == 1);
  p3: assert final (0.25 && 1);
  p4: assert final (!(!0.25));
  // non-constants
  p5: assert final (i == 1 -> (($itor(i) / 4.0) ? 1 : 0) == 1);
  p6: assert final (i == 0 -> ($itor(i) ? 1 : 0) == 0);
  p7: assert final (i == 3 -> ($itor(i) ? 1 : 0) == 1);
endmodule
