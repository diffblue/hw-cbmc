module main(input clk, rst);

  logic data;
  always_ff @(posedge clk) data <= 1'b1;
  assert property(@(posedge clk) disable iff (rst) data);

endmodule
