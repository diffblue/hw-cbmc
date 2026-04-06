module main(input clk);

  reg [2:0] counter = 3;

  // counter decrements but stops at 1, never reaches 0
  always_ff @(posedge clk)
    if(counter > 1)
      counter--;

  wire [2:0] rank = counter;

  rank_decreases: assert property (@(posedge clk)
    !(counter == 0) |=> rank < $past(rank)
  );

  // does not hold: counter never reaches 0
  liveness: assert property (@(posedge clk)
    s_eventually counter == 0
  );

endmodule
