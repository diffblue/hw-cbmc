module main;

  // `__LINE__ is defined in 1800-2017 22.13.
  // Not in 1364-2005.
  initial $display("%d", `__LINE__);

endmodule
