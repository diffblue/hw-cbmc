module main(input clk);

  reg [3:0] x = 0;

  always_ff @(posedge clk)
    x++;

  initial assert property (##[1:2] x == 2);

endmodule
