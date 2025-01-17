module main(input clk, input [31:0] from);

  reg [31:0] x;

  always_ff @(posedge clk)
    x++;

  // The cycle delay must be elaboration-time constant
  initial assert property (##[from:2] x!=10);

endmodule
