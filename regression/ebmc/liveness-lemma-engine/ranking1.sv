module main(input clk);

  parameter max = 100;
  reg [31:0] counter = max;

  always_ff @(posedge clk)
    if(counter == 0)
      counter = max;
    else
      counter--;

  wire [31:0] rank = counter;

  // should be proven by induction
  rank_decreases: assert property (@(posedge clk) !(counter == 0) |=> rank < $past(rank));

  // should be implied by the above
  liveness: assert property (@(posedge clk) s_eventually counter == 0);

endmodule
