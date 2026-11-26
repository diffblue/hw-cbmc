module main(input [7:0] a);

  // The streaming operators are defined in 1800-2017 11.4.14.
  // Not in 1364-2005.
  wire [7:0] b = {<<{a}};

endmodule
