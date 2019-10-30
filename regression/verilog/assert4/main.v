module main();
`define SIZE 31
`define plus_binary(a,b) \
   a+b
   
   reg [`SIZE:0] x;
  wire clk;
  
  initial x=1;
  
  always @(posedge clk) x<=`plus_binary(x,1);

  always assert property1: x!=10;

endmodule
