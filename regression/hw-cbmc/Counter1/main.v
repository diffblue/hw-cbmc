module top(input clk);

  reg [63:0] variable;

  initial variable=0;

  always @(posedge clk)
    variable=variable+1;

  // don't confuse with module
  reg [10:0] top;

endmodule
