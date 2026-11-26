module main(input clk, input en);

  reg [1:0] cnt;
  initial cnt = 0;

  always @(posedge clk)
    if(en)
      cnt = cnt + 1;

  // refuted by a lasso where en stays low
  p0: assert property (always s_eventually cnt == 3);

endmodule
