module main;

  wire [31:0] x = 10;

  property x_is_ten;
    x == 10
  endproperty : x_is_ten

  assert property (x_is_ten);

endmodule
