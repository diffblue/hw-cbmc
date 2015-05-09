module top(x, y, z);

  input [7:0] y, z;
  output [9:0] x;
  reg [5:0] x;

  always @(y or z)
    x = { y[5:2], z[6:1] };  

endmodule
