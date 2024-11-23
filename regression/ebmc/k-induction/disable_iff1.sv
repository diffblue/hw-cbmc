module main(input clk, reset);

  reg [31:0] x;

  always @(posedge clk)
    if(reset)
      x<=1;
    else if(x<10)
      x<=x+1;

  p1: assert property (disable iff (reset) x<=10);

endmodule
