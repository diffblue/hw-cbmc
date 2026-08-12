module main;

  // End label after the "end" of a named generate block,
  // IEEE 1800-2017 27.6.
  if (1)
  begin : g1
    wire [7:0] w = 8'd42;
    initial p0: assert (w == 42);
  end : g1

endmodule
