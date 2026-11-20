module top(input wire [1:0][7:0] a, input wire s,
           output wire [7:0] y);
  assign y = a[s];
endmodule
