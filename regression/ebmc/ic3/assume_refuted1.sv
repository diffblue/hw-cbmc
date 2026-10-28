module main(input clk, input en);

  // The input en is constrained to be TRUE.
  a0: assume property (en);

  reg [1:0] cnt = 0;

  // cnt only advances while en is TRUE; the assumption forces this.
  always @(posedge clk)
    if(en)
      cnt <= cnt + 1;

  // Refuted: cnt reaches 3 because en is assumed TRUE in every step.
  // The counterexample must respect the SVA assumption on the input en.
  p0: assert property (cnt != 3);

endmodule
