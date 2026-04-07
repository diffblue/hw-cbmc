module main(input clk);

  reg [3:0] cnt = 0;
  reg [3:0] shadow = 0;
  always_ff @(posedge clk) cnt <= cnt + 1;
  always_ff @(posedge clk) shadow <= shadow + 1;

  // true for the first 15 cycles
  p0: assert property (cnt != 4'hf);

  // invariant: cnt and shadow are always equal
  p1: assert property (cnt == shadow);

endmodule
