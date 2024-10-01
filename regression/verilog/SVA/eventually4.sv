module main(input a);

  // should pass for any bound
  assert property ((s_eventually !a) or (always a));

endmodule
