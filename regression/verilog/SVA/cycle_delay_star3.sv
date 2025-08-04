module main(input clk);

  reg [2:0] x;

  initial x=0;

  // 0, 1, 2, 3, 4, 4, ...
  always @(posedge clk)
    if(x<=3) x++;

  // passes -- 4 is reached
  initial p0: assert property (##[*] x==4);

endmodule
