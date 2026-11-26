module main(input clk, input x);

  // $past is a 1800-2017 system function (20.13).
  // Not in 1364-2005.
  reg y;
  always @(posedge clk) y <= $past(x);

endmodule
