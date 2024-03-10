module main(input clk, input reset);

  reg [7:0] counter;
  initial counter = 0;
  always @(posedge clk) counter = 0;

  // expected to fail
  p0: assert property (eventually [0:2] counter == 3);

endmodule
