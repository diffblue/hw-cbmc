module main(input clk, input x);

  reg [1:0] cnt;

  initial cnt = 0;

  always @(posedge clk) cnt = cnt + 1;

  lib_counter my_lib(clk);

  p1: assert property (@(posedge clk) cnt != 3);

endmodule
