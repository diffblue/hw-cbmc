module main(input clk);

  reg [7:0] counter = 0;

  always_ff @(posedge clk)
    if(counter == 100)
      counter = 0;
    else
      counter++;

  // wrong ranking function: counter increases, not decreases
  wire [7:0] rank = counter;

  rank_decreases: assert property (@(posedge clk)
    !(counter == 100) |=> rank < $past(rank)
  );

  liveness: assert property (@(posedge clk)
    s_eventually counter == 100
  );

endmodule
