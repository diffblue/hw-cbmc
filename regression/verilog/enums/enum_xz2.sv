module main;

  // 1800-2017 6.19: an unassigned name must not follow a name with x/z
  enum integer { A = 0, B = 'x, C } my_enum;

endmodule
