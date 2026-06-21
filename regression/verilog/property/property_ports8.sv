package some_package;

  parameter x = 10;

  property x_is(value);
    x == value
  endproperty : x_is

endpackage

module main(input clk);

  default clocking @(posedge clk);
  endclocking

  // should pass
  assert property (some_package::x_is(10));

endmodule
