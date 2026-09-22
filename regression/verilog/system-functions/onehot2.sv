module main(input clk, input [3:0] x);

  // $onehot0(x) is true iff at most one bit of x is set
  assume property (@(posedge clk) $onehot0(x));

  // hence, no two bits can be set simultaneously
  p0: assert property (@(posedge clk) !(x[0] && x[1]));
  p1: assert property (@(posedge clk) $countones(x) <= 1);

  // the assumption still permits x to be zero
  p2: assert property (@(posedge clk) x != 0);

  // and permits any single bit to be set
  p3: assert property (@(posedge clk) x != 4'b0100);

endmodule
