module main(input clk);

 reg [7:0] t;

 always_ff @(posedge clk) t = 5;

 initial p1: assert property (t == 0);
 initial p2: assert property (##1 t == 5);

endmodule
