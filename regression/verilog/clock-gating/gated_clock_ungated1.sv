module main(input clk1, clk2, input en, sel, rst_n, input d,
  output reg q1, q2, q3, q4, q5, r1, r2);

  wire mux = sel ? clk1 : clk2;
  wire g1 = clk1 & en;
  wire lonely = en & sel;
  wire other = {clk1, en} == 2'b11;

  // a multiplexer between two base clocks is not gated
  always @(posedge mux) q1 <= d;

  // an asynchronous reset makes the construct execute in every step
  always @(posedge g1 or negedge rst_n)
    if(!rst_n) q2 <= 0; else q2 <= d;

  // neither en nor sel is a base clock
  always @(posedge lonely) q3 <= d;

  // the edge on clk2 is not gated
  always @(posedge g1 or posedge clk2) q4 <= d;

  // logic that is not recognised as gating
  always @(posedge other) q5 <= d;

  // the base clocks
  always @(posedge clk1) r1 <= d;
  always @(posedge clk2) r2 <= d;
endmodule
