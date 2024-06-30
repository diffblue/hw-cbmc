module main;

  wire [7:0] unconnected;

  p1: assert property (unconnected == 10);

endmodule
