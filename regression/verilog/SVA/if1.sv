module main(input clk);

  // count up from 0 to 10
  reg [7:0] counter;

  initial counter = 0;

  always @(posedge clk)
    counter = counter + 1;

  // expected to pass
  p0: assert property (if(counter == 0) nexttime counter == 1);

  // expected to fail
  p1: assert property (if(counter == 0) nexttime counter == 1 else nexttime counter == 3);

endmodule
