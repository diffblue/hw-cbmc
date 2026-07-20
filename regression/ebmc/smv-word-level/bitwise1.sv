module main;

  wire [7:0] a = 8'hA5;
  wire [7:0] b = 8'h3C;
  wire [7:0] w_and = a & b;
  wire [7:0] w_or = a | b;
  wire [7:0] w_xor = a ^ b;
  wire [7:0] w_xnor = a ~^ b;
  wire [7:0] w_not = ~a;

endmodule
