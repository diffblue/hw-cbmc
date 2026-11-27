module main(input clk);

  reg [1:0] cnt;
  initial cnt = 0;

  always @(posedge clk)
    cnt = cnt + 1;

  // holds
  p0: assert property (always s_eventually cnt == 3);

endmodule
