checker myChecker;
  typedef int some_name;
endchecker

module main;
  // checkers have a scope, the typedef is not visible.
  int some_name;
endmodule
