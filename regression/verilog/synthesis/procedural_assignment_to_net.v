module main(input i);

  wire some_net;

  // should error
  always @i some_net = i;

endmodule
