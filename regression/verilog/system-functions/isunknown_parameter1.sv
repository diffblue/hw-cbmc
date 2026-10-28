// $isunknown applied to bit-selects of a four-state parameter
// (IEEE 1800-2017 11.5.1, 20.9).
module main;
  localparam logic [3:0] C = 4'b1x10;
  p0: assert final ($isunknown(C[2]) == 1);
  p1: assert final ($isunknown(C[3]) == 0);
  // reading out of bounds yields x
  p2: assert final ($isunknown(C[5]) == 1);
endmodule
