module my_module(input a, b, c);

endmodule

module main();

  // Null elements in a list of named port connections leave the
  // corresponding ports unconnected.  Per 1800-2017 A.4.1.1, null elements
  // are permitted in ordered_port_connection only; the constructs below are
  // an extension.

  // a trailing null element
  my_module m1(.a(1), .c(1), );

  // several consecutive null elements
  my_module m2(.a(1), , , .c(1));

  // nothing but null elements after the first connection
  my_module m3(.a(1), , );

  initial assert (m1.a == 1 && m1.c == 1);
  initial assert (m2.a == 1 && m2.c == 1);
  initial assert (m3.a == 1);

endmodule
