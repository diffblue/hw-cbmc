module main(input clk);

  reg [31:0] some_value;

  initial some_value = 1;

  always @(posedge clk)
    some_value = some_value + 1;

endmodule
