module main;

  enum { FOO, BAR } some_enum;
  struct { bit s, t; } some_struct;

  // The $typenames for enums and structs are not well standardised,
  // and vary across tools and tool versions.
  assert final ($typename(some_enum)=="enum{FOO,BAR}");
  assert final ($typename(some_struct)=="struct{bit s;bit t;}");

endmodule
