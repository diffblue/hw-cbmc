module submodule;
  parameter P1 = 1;
  parameter P2 = P1 + 1;
endmodule

module main;
  // error: parameter value must be constant
  wire [31:0] some_wire;
  submodule #(some_wire) s1();
endmodule
