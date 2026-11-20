module main(input [7:0] x);

  localparam W = 2;

  // the slice size of a streaming operator may be a constant
  // expression, 1800-2017 11.4.14
  wire [7:0] y = {<<W{x}};

  p0: assert property (y == {x[1:0], x[3:2], x[5:4], x[7:6]});

endmodule
