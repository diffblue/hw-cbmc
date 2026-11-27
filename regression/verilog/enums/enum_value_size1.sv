module main;

  // 1800-2017 6.19: a sized literal must match the size of the base type
  enum logic [2:0] { A = 3'h2, B = 4'h3 } my_enum;

endmodule
