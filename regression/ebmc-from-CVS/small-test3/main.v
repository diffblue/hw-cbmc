module main();

  wire [31:0] x=1+2;

  always assert prop1: x==3;

endmodule
