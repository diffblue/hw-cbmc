// `" is defined in 1800-2017 22.5.1.
// Not in 1364-2005.
`define S(x) `"x`"

module main;

  initial $display(`S(abc));

endmodule
