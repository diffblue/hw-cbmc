module main();

  reg [31:0] x;
  wire clk;
  
  initial x=1;
  
  always @(posedge clk) x<=x+1;

  always assert property1: x!=10;

endmodule
