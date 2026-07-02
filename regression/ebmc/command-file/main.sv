module main(input clk, input x);

  reg y;

  always @(posedge clk)
    y <= x;

  assert property (@(posedge clk) x |=> y);

endmodule
