module main;

  struct { bit s, t; } some_struct;

  // The $typenames for structs are not well standardised,
  // and vary across tools and tool versions.
  initial assert($typename(some_struct)=="struct{bit s;bit t;}");

endmodule
