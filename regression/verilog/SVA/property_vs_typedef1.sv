typedef int some_name;

module main;

  // The identifier 'some_name' can be re-used in the module scope.
  // This works with VCS 2023.03, Questa 2024.3, Xcelium 23.09,
  // Riviera Pro 2023.04.
  property some_name;
    1
  endproperty : some_name

endmodule
