module my_module(input a, b, c);

endmodule

module main();

  // A null element in a port connection list denotes an unconnected port.
  // Per 1800-2017 A.4.1.1, list_of_port_connections permits null elements
  // in ordered_port_connection only; named_port_connection has no such
  // alternative.  The construct below nevertheless occurs in practice, with
  // the null element carrying no information beyond leaving b unconnected.
  my_module m1(.a(1), , .c(1));

  initial assert (m1.a == 1);
  initial assert (m1.c == 1);

endmodule
