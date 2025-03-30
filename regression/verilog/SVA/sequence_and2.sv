module main(input clk);

  reg [31:0] x = 0;

  always @(posedge clk)
    x<=x+1;

  // The end-point of the 'and' sequence is the _later_ of end-points
  // of the arguments.
  initial p1: assert property ((1 and ##2 1) |-> x == 2);

  initial p2: assert property ((##2 1 and 1) |-> x == 2);

endmodule
