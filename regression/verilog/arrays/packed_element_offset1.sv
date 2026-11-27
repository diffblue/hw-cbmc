module main(input [1:0] i);
  wire [1:2][3:0] a = 8'h5A;  // a[1] = 4'h5, a[2] = 4'hA
  wire [3:0] r = a[i];
  p: assert property (i != 2 || r == 4'hA);
endmodule
