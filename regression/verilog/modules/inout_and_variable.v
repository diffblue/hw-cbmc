module sub(inout some_port);

endmodule

module main;
  // 1800-2017 6.5
  // "Variables cannot be connected to either side of an inout port"
  reg my_var;

  sub sub(my_var);

endmodule
