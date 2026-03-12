module main;

  wire [31:0] packed1;
  wire [0:7] packed2;

  wire unpacked1 [3:0];
  wire unpacked2 [0:3];
  wire unpacked3 [8];

  p0: assert final ($size(packed1) == 32);
  p1: assert final ($size(packed2) == 8);
  p2: assert final ($size(unpacked1) == 4);
  p3: assert final ($size(unpacked2) == 4);
  p4: assert final ($size(unpacked3) == 8);

endmodule
