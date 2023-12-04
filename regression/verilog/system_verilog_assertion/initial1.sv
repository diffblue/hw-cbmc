module main(input clk);

  // count up from 0 to 10
  reg [7:0] counter;

  initial counter = 0;

  always @(posedge clk)
    if(counter == 10)
      counter = 0;
    else
      counter = counter + 1;

  // expected to pass
  initial p0: assert property (counter == 0);

  // expected to pass if there are timeframes 0 and 1
  initial p1: assert property (s_nexttime counter == 1);

endmodule
