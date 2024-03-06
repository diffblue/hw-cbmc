// count down from 10 to 0

module main(input clk);

  reg [3:0] counter;

  initial counter = 0;

  always @(posedge clk)
    if(counter != 10)
      counter = counter + 1;

  // expected to pass
  p0: assert property (s_eventually counter == 10);

endmodule
