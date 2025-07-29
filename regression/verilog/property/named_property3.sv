module main;

  wire [31:0] x = 'b10010001;

  property with_index;
    x[7:4] == 'b1001
  endproperty

  assert property (with_index);

endmodule
