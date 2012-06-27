module top(input clk, input enable);

  reg [63:0] variable;

  initial variable=0;

  always @(posedge clk)
    if(enable)
      variable=variable+1;

endmodule
