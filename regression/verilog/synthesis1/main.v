module main();
  reg [31:0] t;

  always @(*) t=t+1;

  // should fail
  always assert p1: 0;

endmodule
