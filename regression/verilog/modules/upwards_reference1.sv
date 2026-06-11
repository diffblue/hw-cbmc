module top;
  parameter P = 123;
  sub sub();
endmodule

module sub;
  // an upwards reference to a parameter
  initial assert(top.P == 123);
endmodule
