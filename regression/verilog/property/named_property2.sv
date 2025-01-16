module main(input clk);

  reg [31:0] x = 0;
  always_ff @(posedge clk) x++;

  property x_is_eventually_ten;
    s_eventually x == 10
  endproperty : x_is_eventually_ten

  assert property (x_is_eventually_ten);

endmodule
