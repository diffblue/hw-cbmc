module main(input clk);

  // an array of bytes
  reg [7:0] some_array [32];

  assert property (@(posedge clk) some_array[0] == 8'd123);

endmodule
