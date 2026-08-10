module lib_counter(input clk);

  reg [3:0] cnt;

  initial cnt = 0;

  always @(posedge clk) cnt = cnt + 1;

endmodule
