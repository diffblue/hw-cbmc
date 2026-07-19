module main;

  typedef bit some_type;
  typedef int signed other_type;

  // typedefs are expanded
  initial assert($typename(some_type)=="bit");
  initial assert($typename(other_type)=="int");

endmodule
