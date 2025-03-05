module main(input clk);

  // The RHS must be a sequence
  assert property (@(posedge clk) (always 1) |-> 1);

endmodule : main
