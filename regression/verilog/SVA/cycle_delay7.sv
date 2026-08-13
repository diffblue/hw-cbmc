module main(input clk);

  reg [31:0] x;

  always_ff @(posedge clk)
    x++;

  // The cycle delay must not be negative.
  initial assert property (##(-1) x != 10);

endmodule
