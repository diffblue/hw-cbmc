module main;

  wire a;

  // $root is defined in 1800-2017 23.9.
  // Not in 1364-2005.
  wire b = $root.main.a;

endmodule
