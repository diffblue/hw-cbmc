module main(input clk);

  reg [3:0] x = 0;

  always_ff @(posedge clk)
    x++;

  initial assert property (x == 0 ##1 x == 1 ##1 x == 2 ##1 x == 3);

endmodule
