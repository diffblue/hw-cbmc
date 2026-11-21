// Initial-state constraints that are not reset values.
module main(input clk, input a);
  reg r, t;
  initial r = a;
  initial t = a;
  always @(posedge clk) begin
    r <= r;
    t <= t;
  end
  p1: assert property (@(posedge clk) r == t);  // holds
  p2: assert property (@(posedge clk) r == 0);  // fails
endmodule
