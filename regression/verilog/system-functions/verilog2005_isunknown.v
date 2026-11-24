module main(input [7:0] x);

  // $isunknown is a 1800-2017 system function (20.9).
  // Not in 1364-2005.
  wire y = $isunknown(x);

endmodule
