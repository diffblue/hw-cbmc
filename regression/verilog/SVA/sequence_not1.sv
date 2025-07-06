module main(input clk);

  reg [31:0] x = 0;

  always @(posedge clk)
    x<=x+1;

  // Given a sequence, 'not' yields a property, not a sequence
  assert property ((not x == 1)[*1]);

endmodule
