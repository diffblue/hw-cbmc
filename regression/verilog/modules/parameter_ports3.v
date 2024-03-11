module sub #(parameter p = 1, localparam derived = p+1)();

  always assert p1: derived == 124;

endmodule

module main;

  sub #(123) submodule();

endmodule // main
