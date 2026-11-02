module main;

  // w has no driver, and is read by both a and b,
  // which must see the same value
  wire w;
  wire a = w;
  wire b = !w;

  p0: assert property (a != b);
  p1: assert property (a == w);

endmodule
