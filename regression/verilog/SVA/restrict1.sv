module main(input clk, input en);

  reg [31:0] x;

  initial x=0;

  always @(posedge clk)
    if(en)
      x<=x+1;

  p0: restrict property (x!=5);

  p1: assert property (x!=6);

endmodule
