module main(input clk);

  reg [3:0] counter = 0;

  always @(posedge clk)
    counter++;

  // $past(counter, 1) is deliberately not used
  assert property (counter >= 2 -> $past(counter, 2) == counter - 2);

endmodule
