module main(input clk, input en);

  reg [7:0] cnt;
  initial cnt = 0;

  // the counter increments when enabled
  always @(posedge clk)
    if(en)
      cnt = cnt + 1;

  // fails at depth 7, i.e., a counterexample with 8 states
  p0: assert property (cnt != 7);

  // holds
  p1: assert property (cnt <= 200);

endmodule
