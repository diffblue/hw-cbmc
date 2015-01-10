module main();

  reg [31:0] x;
  wire clk;
  
  initial x=1;
  
  always @(posedge clk)
    if(x<1000)
      x<=x+1;

  always assert property1: x<=1000;

endmodule
