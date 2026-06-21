module main(input clk);

  default clocking @(posedge clk);
  endclocking

  wire [31:0] x = 10;

  property x_is(bit [31:0] value);
    x == value
  endproperty : x_is

  assert property (x_is(10));

endmodule
