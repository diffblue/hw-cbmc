module main(input [7:0] data);

  // Allowed; only the LSB will be considered.
  always @(posedge data);

endmodule
