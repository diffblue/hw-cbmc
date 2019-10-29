module main();
`define SIZE 31
`define plus_one(a) a+1
   
  reg [`SIZE:0] x;
  wire clk;
  
  initial x=1;
  
  always @(posedge clk) x<=`plus_one(x);

  always assert property1: x!=10;

endmodule
