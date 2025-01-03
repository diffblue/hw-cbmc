module top(input clk);

  reg important;
  reg not_important;

  initial important = 1;
  always @(posedge clk)
    important = important;

  assert property (important == 1);

endmodule
