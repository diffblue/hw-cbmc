// count down from 10 to 0

module main(input clk);

  reg [7:0] counter;

  initial counter = 0;

  always @(posedge clk)
    if(counter != 100)
      counter++;
    else
      counter = 0;

  // expected to pass
  p0: assert property (s_eventually counter == 0);

endmodule
