module main(input clk);

  // count up
  reg [7:0] counter = 0;

  always_ff @(posedge clk)
    counter++;

  // expected to pass
  p0: assert property (@(posedge clk) disable iff (counter == 0) counter != 0);

  // expected to pass vacuously
  p1: assert property (@(posedge clk) disable iff (1) 0);

  // expected to fail when counter reaches 2
  p2: assert property (@(posedge clk) disable iff (counter == 1) counter == 0);

endmodule
