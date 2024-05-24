module main(input [31:0] some_input);

  wire [31:0] x = 456 + some_input;

  sub sub();

endmodule

module sub;

  wire [31:0] x = 123;

endmodule
