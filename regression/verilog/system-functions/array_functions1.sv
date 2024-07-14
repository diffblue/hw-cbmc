module main;

  wire [32:1] packed1;
  wire [0:31] packed2;

  wire unpacked1 [32:1];
  wire unpacked2 [0:31];
  wire unpacked3 [32];

  pP0: assert final ($left(packed1) == 32 && $right(packed1) == 1);
  pP1: assert final ($left(packed2) == 0 && $right(packed2) == 31);
  pP2: assert final ($low(packed1) == 1 && $high(packed1) == 32);
  pP3: assert final ($low(packed2) == 0 && $high(packed2) == 31);
  pP4: assert final ($increment(packed1) == 1);
  pP5: assert final ($increment(packed2) == -1);

  pU0: assert final ($left(unpacked1) == 32 && $right(unpacked1) == 1);
  pU1: assert final ($left(unpacked2) == 0 && $right(unpacked2) == 31);
  pU2: assert final ($left(unpacked3) == 31 && $right(unpacked3) == 0);
  pU3: assert final ($low(unpacked1) == 1 && $high(unpacked1) == 32);
  pU4: assert final ($low(unpacked2) == 0 && $high(unpacked2) == 31);
  pU5: assert final ($low(unpacked3) == 0 && $high(unpacked3) == 31);
  pU6: assert final ($increment(unpacked1) == 1);
  pU7: assert final ($increment(unpacked2) == -1);
  pU8: assert final ($increment(unpacked3) == 1);

endmodule
