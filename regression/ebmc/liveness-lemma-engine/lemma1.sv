module main(input clk);

  reg [7:0] counter = 100;

  always_ff @(posedge clk)
    if(counter == 0)
      counter = 100;
    else
      counter--;

  wire [7:0] rank = counter;

  rank_decreases: assert property (@(posedge clk)
    !(counter == 0) |=> rank < $past(rank)
  );

  liveness: assert property (@(posedge clk)
    s_eventually counter == 0
  );

endmodule
