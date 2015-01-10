module main();

  reg [31:0] x;
  wire clk;
  
  initial x=1;
  
  always @(posedge clk) x<=x+$ND(1, 2, 3);

  // this will fail after 3 ticks
  always assert property1: x!=10;

endmodule
