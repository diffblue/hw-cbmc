module main(input clk, input data);

  reg some_register;
  
  initial some_register = 0;

  always @(posedge clk)
    some_register = some_register || data;

endmodule
