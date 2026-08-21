module child(input i, output reg o);

  always @(*) o = ~i;

endmodule

module main;

  // The genvar declared in the loop header is local to the loop, 1800-2017
  // 27.4, and must be resolvable when it is used to index the actual of an
  // output port, which is checked as an lvalue.

  wire [3:0] d = 4'b1010;
  wire [3:0] q;

  for (genvar g = 0; g < 4; g++)
  begin : blk
    child c(.i(d[g]), .o(q[g]));
  end

  always assert p1: q == 4'b0101;

endmodule
