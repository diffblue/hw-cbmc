module main(input clk, input i);

  // a and b form a combinational loop. a == !b and b == a is
  // unsatisfiable, so the model has no traces, and every property
  // holds vacuously. The cone-of-influence reduction must not
  // drop these two definitions.
  wire a, b;
  assign a = !b;
  assign b = a;

  reg r;
  initial r = 0;
  always @(posedge clk) r <= i;

  p0: assert property (r == 0);

endmodule
