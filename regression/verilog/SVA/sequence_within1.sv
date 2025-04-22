module main(input clk);

  reg [7:0] x = 0;

  always @(posedge clk)
    x<=x+1;

  // fails, no rhs match
  initial p0: assert property (x == 0 within x == 1);

  // passes, lhs match at beginning of rhs match
  initial p1: assert property (x == 0 within ##10 1);

  // passes, lhs match in the middle of rhs match
  initial p2: assert property (x == 5 within ##10 1);

  // passes, lhs match at the end of rhs match
  initial p3: assert property (x == 10 within ##10 1);

  // fails, lhs match just beyond the rhs match
  initial p4: assert property (x == 11 within ##10 1);

endmodule
