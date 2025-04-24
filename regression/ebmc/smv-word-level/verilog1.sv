module main(input clk);

  reg [31:0] x;

  initial x = 0;

  always @(posedge clk)
    x = x + 1;

  initial assert property (s_eventually x == 10);

endmodule
