module main;

  wire [31:0] x = 10;

  property is_ten(something);
    something == 10
  endproperty : is_ten

  assert property (is_ten(x));

endmodule
