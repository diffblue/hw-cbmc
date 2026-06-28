module main(input clk, input d, output reg q);

  specify
    specparam trise = 2, tfall = 3;
  endspecify

  always @(posedge clk)
    q <= d;

endmodule
