module main;

  // $test$plusargs returns 0 (not found) in synthesis
  always assert ($test$plusargs("TESTNAME") == 0);

endmodule
