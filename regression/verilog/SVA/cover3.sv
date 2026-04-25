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
  p0: cover property (counter == 1 and s_nexttime counter == 2);

  // expected to fail
  p1: cover property (counter == 1 and s_nexttime counter == 3);

  // expected to fail
  p2: cover property (disable iff (counter == 1) s_nexttime counter == 2);

endmodule
