module main(input clk, input c);

  // values of chandle variables in traces
  chandle h = null;
  bit b = 0;

  always @(posedge clk)
    b = c;

  p0: assert property (h == null);
  p1: assert property (b == 0);

endmodule
