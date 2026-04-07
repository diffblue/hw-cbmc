module main;

  wire some_data = $ND(1'b0, 1'b1);

  // should fail
  assert property (some_data);

endmodule
