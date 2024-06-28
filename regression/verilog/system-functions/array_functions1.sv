module main;

  wire [32:1] packed1;
  wire [0:31] packed2;

  wire unpacked1 [32:1];
  wire unpacked2 [0:31];
  wire unpacked3 [32];

  pP0: assert property ($left(packed1) == 32 and $right(packed1) == 1);
  pP1: assert property ($left(packed2) == 0 and $right(packed2) == 31);
  pP2: assert property ($low(packed1) == 1 and $high(packed1) == 32);
  pP3: assert property ($low(packed2) == 0 and $high(packed2) == 31);
  pP4: assert property ($increment(packed1) == 1);
  pP5: assert property ($increment(packed2) == -1);

  pU0: assert property ($left(unpacked1) == 32 and $right(unpacked1) == 1);
  pU1: assert property ($left(unpacked2) == 0 and $right(unpacked2) == 31);
  pU2: assert property ($left(unpacked3) == 31 and $right(unpacked3) == 0);
  pU3: assert property ($low(unpacked1) == 1 and $high(unpacked1) == 32);
  pU4: assert property ($low(unpacked2) == 0 and $high(unpacked2) == 31);
  pU5: assert property ($low(unpacked3) == 0 and $high(unpacked3) == 31);
  pU6: assert property ($increment(unpacked1) == 1);
  pU7: assert property ($increment(unpacked2) == -1);
  pU8: assert property ($increment(unpacked3) == 1);

endmodule
