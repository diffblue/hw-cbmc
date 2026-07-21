module main(input sel);

  wire [7:0] a = 8'd10;
  wire [7:0] b = 8'd3;
  wire [7:0] mux = sel ? a : b;

endmodule
