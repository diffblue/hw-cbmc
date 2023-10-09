module main(input [31:0] input1);

  wire clk;
  reg [31:0] some_reg = 0;

  always @(posedge clk)
    some_reg  = input1;

endmodule
