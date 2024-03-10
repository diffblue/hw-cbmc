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
  p0: assert property (s_eventually counter == 10);

endmodule
