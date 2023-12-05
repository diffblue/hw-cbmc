// count down from 10 to 0
module my_counter(input clk);

  reg [3:0] counter;

  initial counter = 10;

  always @(posedge clk)
    if(counter != 0)
      counter = counter - 1;

endmodule

module main(input clk);

  my_counter instance(clk);

  // expected to pass with ranking function instance.counter
  p0: assert property (eventually instance.counter == 0);

endmodule
