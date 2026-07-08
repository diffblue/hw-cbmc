module main(input clk);

  reg [3:0] cnt = 0;

  always @(posedge clk)
    if(cnt != 5)
      cnt = cnt + 1;

  // reachable
  p0: cover property (cnt == 5);

  // unreachable
  p1: cover property (cnt == 8);

endmodule
