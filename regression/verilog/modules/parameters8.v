module submodule;
  parameter P1 = 1;
  parameter P2 = P1 + 1;
endmodule

module main;
  submodule #(10) s1();
endmodule
