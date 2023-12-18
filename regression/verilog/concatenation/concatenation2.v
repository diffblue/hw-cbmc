module main;
  parameter signed [3:0] A = -1;
  parameter B = {A};
  always assert pA: A == -1;
  always assert pB: B == 15;
endmodule
