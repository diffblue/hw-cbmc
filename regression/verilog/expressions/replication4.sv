module main;

  // Per 1800-2017 11.4.12.1, a replication with a zero replication constant
  // is legal inside a concatenation that has at least one operand of nonzero
  // size.  Its size is zero, and it contributes nothing to the result.

  // In a constant expression.
  localparam [3:0] p = {2'b10, {0{1'b1}}, 2'b01};

  // The very same expression in a non-constant context.
  wire [3:0] x = {2'b10, {0{1'b1}}, 2'b01};

  initial assert (p == 4'b1001);
  initial assert (x == 4'b1001);

endmodule
