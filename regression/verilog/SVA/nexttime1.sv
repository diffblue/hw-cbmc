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
  initial p1: assert property (s_nexttime[0] counter == 0);

  // expected to pass
  initial p2: assert property (s_nexttime[1] counter == 1);

  // expected to pass
  initial p3: assert property (nexttime[8] counter == 8);

endmodule
