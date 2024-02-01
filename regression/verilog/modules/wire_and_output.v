module M1(some_port);
  output [31:0] some_port;
  wire [31:0] some_port;
endmodule

module M2(some_port);
  // order flipped
  wire [31:0] some_port;
  output [31:0] some_port;
endmodule
