// A combinational cycle through two nets: the nets may have any value,
// as long as they are equal.
module main(input clk);
  wire a, b;
  assign a = b;
  assign b = a;
  p0: assert property (@(posedge clk) a == b);
  p1: assert property (@(posedge clk) a == 0);         // fails
  p2: assert property (@(posedge clk) a == 1);         // fails
endmodule
