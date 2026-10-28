module main;

  // Per 1800-2017 11.4.12.1, a replication with a zero replication constant
  // is only legal when it appears directly within a concatenation.
  // This one does not, and hence is an error.
  wire [3:0] x = {0{1'b1}};

endmodule
