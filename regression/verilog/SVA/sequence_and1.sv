module main(input clk);

  reg [31:0] x = 0;

  always @(posedge clk)
    x<=x+1;

  // should fail
  initial p0: assert property (x == 0 and x == 1);

  // Given two sequences, 'and' yields a sequence, not a property
  initial p1: assert property ((x == 0 and x == 1)[*1]);

endmodule
