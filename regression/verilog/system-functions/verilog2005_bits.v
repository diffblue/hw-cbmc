module main(input [7:0] x);

  // $bits is a 1800-2017 system function (20.6.2).
  // Not in 1364-2005.
  wire [31:0] y = $bits(x);

endmodule
