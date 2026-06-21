module main(input clk);

  default clocking @(posedge clk);
  endclocking

  wire [31:0] x = 10;

  property x_is(int values[3]);
    x == values[0] || x == values[1] || x == values[2]
  endproperty : x_is

  // should fail
  int values_to_try[3] = '{1, 2, 3};
  assert property (x_is(values_to_try));

endmodule
