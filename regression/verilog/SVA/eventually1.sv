module main(input clk, input reset);

  // count up from 0 to 10
  reg [7:0] counter;
  initial counter = 0;

  always @(posedge clk)
    if(counter != 10)
      counter = counter + 1;

  // expected to pass
  p0: assert property (counter == 1 implies eventually [1:2] counter == 3);

endmodule
