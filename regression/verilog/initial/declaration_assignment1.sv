module main;

  // 1800 2017 10.5
  // variable declaration assignments happen before any initial
  // or always procedures
  int some_data = 123;

  initial assert(some_data == 123);
  always assert property(some_data == 123);

endmodule
