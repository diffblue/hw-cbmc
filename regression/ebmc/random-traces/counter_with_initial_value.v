module main(input [7:0] input1);

  wire clk;
  reg [7:0] some_reg;
  initial some_reg = input1;

  always @(posedge clk)
    if(some_reg != 0)
      some_reg = some_reg - 1;

endmodule
