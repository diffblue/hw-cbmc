module main();

  reg [31:0] x;
  wire clk;
  
  initial x=1;
  
  always @(posedge clk) x<=x+1;

  assert property (x!=10);

  //assert property (@(posedge clk) x!=10);

endmodule
