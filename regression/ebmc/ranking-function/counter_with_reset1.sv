// count up from 0 to 10

module main(input clk, input reset);

  reg [3:0] counter;

  initial counter = 0;

  always @(posedge clk)
    if(reset)
      counter = 0;
    else if(counter != 10)
      counter = counter + 1;

  // expected to fail, owing to reset
  p0: assert property (eventually counter == 10);

  // expected to pass
  p1: assert property (eventually (reset || counter == 10));

endmodule
