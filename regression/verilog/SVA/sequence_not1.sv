module main(input clk);

  reg [31:0] x = 0;

  always @(posedge clk)
    x<=x+1;

  // should pass
  initial p0: assert property (not x == 1);

  // Given a sequence, 'not' yields a sequence, not a property
  initial p1: assert property ((not x == 1)[*1]);

endmodule
