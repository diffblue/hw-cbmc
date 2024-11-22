module main(input clk);

  reg [31:0] counter = 0;

  always @(posedge clk)
    counter++;

  assert property ($past(counter, 0) == counter);

  assert property (counter >= 1 -> $past(counter, 1) == counter - 1);

  assert property (counter >= 2 -> $past(counter, 2) == counter - 2);

  assert property (counter == 0 -> $past(counter, 1) == 0);

  assert property (counter == 1 -> $past(counter, 2) == 0);

endmodule
