module main(input clk);

  reg [7:0] counter;

  initial counter = 0;

  always @(posedge clk)
    if(counter < 10)
      counter = counter + 1;
    else
      counter = 6;

  // expected to fail with any bound greater or equal 11
  p0: assert property (eventually counter<=5);

endmodule
