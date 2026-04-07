module main;

  // 2D packed array concatenated with a bit vector
  logic [3:1][7:0] b = '{ 8'h01, 8'h02, 8'h03 };
  logic [7:0] data = 8'hFF;
  logic [3:0][7:0] a;

  assign a = {b, data};

  assert final(a == 32'h010203FF);

endmodule
