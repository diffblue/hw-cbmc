module top(input clk);

  reg important;
  reg not_important;

  initial important = 1;
  always @(posedge clk)
    important = 0;

  // should fail after one transition
  assert property (important == 1);

endmodule
