module my_module(input a, b, c);

endmodule

module main();

  // A leading null element gives no clue whether an ordered or a named list
  // of port connections follows, and hence remains rejected.  Note that
  // 1800-2017 A.4.1.1 permits null elements in ordered_port_connection only,
  // and that the ordered list below has fewer elements than my_module has
  // ports.
  my_module m1(, .b(1), .c(1));

endmodule
