module top(input clk);

  reg [1:0] counter;

  always @(posedge clk) counter++;

  // The reset condition is counter != 0, which holds in the initial
  // state.
  initial assert property (@(posedge clk) counter != 0);

  // The counter reaches 3 from any state with counter != 0.
  assert property (@(posedge clk) counter != 3);

endmodule
