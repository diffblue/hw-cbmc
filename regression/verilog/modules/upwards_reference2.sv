module top;
  sub #(123) A();
  sub #(456) B();
endmodule

module sub #(value);
  subsub subsub();
endmodule

module subsub;
  // An upwards reference to a parameter.
  // This is both top.A.value and top.B.value, and the
  // assertion fails for top.B.value
  initial assert(sub.value == 123);
endmodule
