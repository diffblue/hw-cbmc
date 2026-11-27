module main(input clk, input en);

  reg [7:0] cnt;
  initial cnt = 0;

  always @(posedge clk)
    if(en)
      cnt = cnt + 1;

  // these fail at different depths
  p0: assert property (cnt != 3);
  p1: assert property (cnt != 9);
  p2: assert property (cnt != 0);
  p3: assert property (cnt != 100);

endmodule
