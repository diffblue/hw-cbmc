module main;

  reg [31:0] x;
  wire clk;

  initial x=0;

  always @(posedge clk)
    x<=x+1;

  // fails when x reaches 10
  p0: assert property (case(x) 10: 0; endcase);

endmodule
