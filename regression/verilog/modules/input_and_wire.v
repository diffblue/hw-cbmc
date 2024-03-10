module M1(some_port);
  input [31:0] some_port;
  wire [31:0] some_port;
endmodule

module M2(some_port);
  // order flipped
  input [31:0] some_port;
  wire [31:0] some_port;
endmodule

module M3(input wire [31:0] some_port);
endmodule
