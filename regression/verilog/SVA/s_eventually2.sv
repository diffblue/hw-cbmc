// count up from 0 to 10, with option to reset

module main(input clk, input reset);

  reg [7:0] counter;

  initial counter = 0;

  always @(posedge clk)
    if(reset)
      counter = 0;
    else if(counter != 10)
      counter = counter + 1;

  // expected to pass for any bound
  p0: assert property (s_eventually (reset || counter == 10));

  // expected to fail, owing to range
  p1: assert property (s_eventually[0:2] (reset || counter == 10));

endmodule
