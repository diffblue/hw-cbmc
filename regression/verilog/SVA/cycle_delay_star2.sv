module main(input clk);

  reg [2:0] x;

  initial x=0;

  // 0, 1, 2, 3, 3, ...
  always @(posedge clk)
    if(x<=3) x++;

  // fails -- 4 is never reached
  initial p0: assert property (##[*] x==4);

endmodule
