property is_ten(int value);
  value == 10
endproperty

module main;

  wire [31:0] x = 10;

  initial assert property (is_ten(x));

endmodule
