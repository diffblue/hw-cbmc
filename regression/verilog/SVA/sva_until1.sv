module main(input a, b);

  wire a, b;

  p0: assert property (a until_with b);
  p1: assert property (a until b);
  p2: assert property (a s_until b);

endmodule
