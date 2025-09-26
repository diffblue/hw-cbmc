// count up from 0 to 10

module main(input clk);

  reg [7:0] counter;

  initial counter = 0;

  always @(posedge clk)
    if(counter == 10)
      counter = 0;
    else
      counter = counter + 1;

  // expected to pass
  p0: assert property (s_eventually counter == 10);

endmodule
