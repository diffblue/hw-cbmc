module sub(x, y);

  input [31:0] x, y;

  always assert eq: x!=y;

endmodule

module main();

  reg [31:0] x;
  wire clk;
  
  initial x=1;
  
  always @(posedge clk)
    if(x<10)
      x<=x+1;

  // this one holds
  sub s_ok(x, 100);
  
  // this one doesn't
  sub s_fail(x, 10);

endmodule
