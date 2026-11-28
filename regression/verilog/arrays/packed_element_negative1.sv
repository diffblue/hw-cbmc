module main(input signed [4:0] neg);
  wire [-5:-2][3:0] a = 16'hA5C3;  // a[-5] = 4'hA, a[-2] = 4'h3
  wire [3:0] r = a[neg];
  p_value: assert property (neg != -2 || r == 4'h3);
  p_reach: assert property (neg != -5);
endmodule
