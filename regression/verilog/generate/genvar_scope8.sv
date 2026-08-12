module child(input i, output o);

  parameter P = 0;

  assign o = (P == 3) ? ~i : i;

endmodule

module main;

  // The genvar declared in the loop header is local to the loop, 1800-2017
  // 27.4, and must be resolvable in the port connections and the parameter
  // values of a module instance, with the value it has in the given
  // iteration of the loop.

  wire [3:0] d = 4'b1010;
  wire [3:0] q;

  for (genvar g = 0; g < 4; g++)
  begin : blk
    child #(.P(g)) c(.i(d[g]), .o(q[g]));
  end

  always assert p1: q == 4'b0010;

endmodule
