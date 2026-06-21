module main(input clk);

  default clocking @(posedge clk);
  endclocking

  wire [31:0] x = 10;

  property x_is(value = 20);
    x == value
  endproperty : x_is

  // should fail
  assert property (x_is());

endmodule
