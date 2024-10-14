module main(input clk);

  reg [31:0] x = 0;

  always @(posedge clk)
    x<=x+1;

  initial p0: assert property (first_match(x == 0));

  // can come with sequence_match_items
  initial p1: assert property (first_match(x == 0, x++));

endmodule
