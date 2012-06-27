module sub1(a);

  input [31:0] a;
  wire [31:0] z;

  assign z=a;

endmodule

module top(input clk);

  reg [31:0] variable;

  initial variable=0;

  always @(posedge clk)
    variable=variable+1;

  sub1 s(variable);

endmodule
