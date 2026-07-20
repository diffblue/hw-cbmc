module main;

  wire [7:0] a = 8'd10;
  wire [7:0] b = 8'd3;
  wire w_lt = a < b;
  wire w_gt = a > b;
  wire w_le = a <= b;
  wire w_ge = a >= b;
  wire w_ne = a != b;

endmodule
