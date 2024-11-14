module main;

  // The section 11.4.12.1 in 1800-2017 is contained in 11.4.12,
  // which suggests that the rules there apply to replication operators.
  // Hence, replications must not use unsized constants.
  wire [31:0] x = {4{'b1010}};

endmodule
