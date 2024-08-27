module main(input clk);

  bit state = 0;

  always_ff @(posedge clk)
    state = 1;

  logic data;

  // continuous assignment to variable
  assign data = state;

  cover1: cover property (@(posedge clk) (1));

endmodule
