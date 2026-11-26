module sub(input a);
endmodule

module main;

  wire a;

  // Implicit .name port connections are defined in 1800-2017 23.3.2.3.
  // Not in 1364-2005.
  sub i(.a);

endmodule
