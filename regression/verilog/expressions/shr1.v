module main();

  wire [15:0] y;

  wire [15:0] x;

  assign x=y*2>>1;

  always assert property1: x==y;

endmodule
