module main(input clk, input c);

  // a design with an event variable
  event e;
  bit b = 0;

  always @(posedge clk)
    b = c;

  p0: assert property (b == 0);

endmodule
