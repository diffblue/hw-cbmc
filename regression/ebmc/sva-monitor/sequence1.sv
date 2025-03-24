module main(input clk);

  reg [31:0] x = 0;

  always_ff @(posedge clk)
    x++;

  initial p0: assert property (x==0 ##1 x==1 ##1 x==2);

endmodule
