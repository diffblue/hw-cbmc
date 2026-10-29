// A vector whose bit 0 is driven by a continuous assignment of a constant,
// and whose bit 1 is driven by the output of a flip-flop in a child module.
// The non-deterministic value of the vector, which the definition of bit 0
// uses for bit 1, was the same in every timeframe, and conflicted with the
// flip-flop's output once that changed. Every property then held
// vacuously.
module sub(input din, input clk, input reset_n, output reg dout);
  always @(posedge clk or negedge reset_n)
    if(~reset_n) dout <= 1'b0; else dout <= din;
endmodule

module main(input clk);
  reg first = 1;
  always @(posedge clk) first <= 0;
  wire rst_n = !first;

  wire [1:0] a;
  assign a[0] = 1'b1;
  sub u(.din(a[0]), .clk(clk), .reset_n(rst_n), .dout(a[1]));

  reg [4:0] warm = 0;
  always @(posedge clk) if(warm != 5'd31) warm <= warm + 5'd1;

  p0: assert property (@(posedge clk) !(warm >= 5'd8));   // fails at 8
  p1: assert property (@(posedge clk) a[0] == 1);
endmodule
