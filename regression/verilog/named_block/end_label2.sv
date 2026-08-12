module main;

  parameter int W = 7;

  // End label after the "join" of a named parallel block,
  // IEEE 1800-2017 9.3.4.
  initial fork : fb
    p0: assert (W == 7);
  join : fb

endmodule
