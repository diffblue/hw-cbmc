typedef int some_name;

module main;

  // The identifier 'some_name' can be re-used in the module scope.
  // This works with VCS 2023.03, Questa 2024.3, Xcelium 23.09,
  // Riviera Pro 2023.04.
  sequence some_name;
    1
  endsequence : some_name

  // some_name is usable as a non-type identifier
  assert property(some_name);

endmodule
