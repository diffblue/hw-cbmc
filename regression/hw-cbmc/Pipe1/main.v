module top(input clk, full0, output reg full2);

  reg full1;

  always @(posedge clk)
    full1<=full0;

  always @(posedge clk)
    full2<=full1;
  
  initial full1=0;
  initial full2=0;

endmodule
