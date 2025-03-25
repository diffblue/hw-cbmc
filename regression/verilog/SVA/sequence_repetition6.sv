module main(input clk);

  // Sequence repetition requires a sequence argument.
  assert property ((s_nexttime 1)[*]);

endmodule
