module main(input clk);

  default clocking @(posedge clk);
  endclocking

  wire [31:0] x = 10;

  property x_is(bit [31:0] value);
    x == value
  endproperty : x_is

  property or_property(property p1, p2);
    p1 or p2
  endproperty

  assert property (or_property(x_is(10), x == 20));

endmodule
