module main(input clk);

  reg [31:0] x;

  initial x = 0;

  always @(posedge clk)
    x = x + 1;

  initial assert property (nexttime[2] x[31:1] == 1);

endmodule
