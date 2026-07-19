module main;

  enum { FOO, BAR } some_enum;

  // The $typenames for enums are not well standardised,
  // and vary across tools and tool versions.
  initial assert($typename(some_enum)=="enum{FOO,BAR}");

endmodule
