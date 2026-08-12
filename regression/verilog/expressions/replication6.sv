module main;

  // Per 1800-2017 11.4.12.1, a replication with a zero replication constant
  // requires a concatenation that has at least one operand of nonzero size.
  wire [3:0] x = {{0{1'b1}}};

endmodule
