// 1800-2017 23.3.1
module somewhere;
  parameter P = 123;
endmodule

module somewhere_else;
  initial assert($root.the_top.A.P == 123);
endmodule

module the_top;
  somewhere A();
  somewhere_else B();
endmodule
