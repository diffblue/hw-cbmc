module main(input clk);

  reg [31:0] x = 0;

  always @(posedge clk)
    x<=x+1;

  initial p0: assert property (x == 0 within x == 1);

endmodule
