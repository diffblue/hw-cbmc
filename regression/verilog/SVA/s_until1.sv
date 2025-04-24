module main(input clk);

  // count up from 0 to 10
  reg [7:0] counter = 0;

  always_ff @(posedge clk)
    if(counter == 10)
      counter = 0;
    else
      counter = counter + 1;

  // expected to pass
  initial p0: assert property ($past(counter)<=counter s_until counter==10);

  // expected to fail
  initial p1: assert property (1 s_until counter==11);

endmodule
