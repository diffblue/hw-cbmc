module top(input clk, input [63:0] in_var);

  reg [63:0] variable;

  initial variable=0;

  always @(posedge clk)
    variable=in_var;

endmodule
