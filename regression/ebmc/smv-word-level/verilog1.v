module main(input clk);

  reg [31:0] x;

  initial x = 0;

  always @(posedge clk)
    x = x + 1;

endmodule
