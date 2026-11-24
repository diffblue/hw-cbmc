module main(input clk, input i);

  // A combinational loop through two nets that has no consistent value:
  // a == !b and b == a. The model hence has no traces, and every property
  // holds vacuously, as word-level BMC reports (see also
  // ebmc/cone-of-influence/cycle1).
  wire a, b;
  assign a = !b;
  assign b = a;

  reg r;
  initial r = 0;
  always @(posedge clk) r <= i;

  p0: assert property (r == 0);

endmodule
