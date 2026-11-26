module main(input clk, input en);

  reg [7:0] cnt;
  initial cnt = 0;

  always @(posedge clk)
    if(en)
      cnt = cnt + 1;

  // covered at depth 4
  c0: cover property (cnt == 4);

  // not covered within bound 10
  c1: cover property (cnt == 20);

endmodule
