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

  // expected to fail
  initial p1: assert property (counter == 100);

  // expected to pass
  initial p2: assert property (##1 counter == 1);

  // expected to fail
  initial p3: assert property (##1 counter == 100);

  // expected to pass if there are timeframes 0 and 1
  initial p4: assert property (s_nexttime counter == 1);

  // expected to pass
  initial p5: assert property (always [1:1] counter == 1);

endmodule
