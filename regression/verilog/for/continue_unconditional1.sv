// An unconditional continue at the end of a loop body (IEEE 1800-2017
// 12.8). The path through the continue is the only path that reaches
// the next iteration, and its path condition is that of the loop body.
module main(input clk, input c);
  reg [3:0] x = 0;
  reg [3:0] y = 0;
  always @(posedge clk) begin
    x = 0;
    for (int i = 0; i < 3; i++) begin
      x = x + 1;
      continue;
      x = 10; // unreachable
    end
    p0: assert (x == 3);

    // an unconditional continue after a conditional one
    y = 0;
    for (int i = 0; i < 3; i++) begin
      if (c) continue;
      y = y + 1;
      continue;
    end
    p1: assert (y == (c ? 0 : 3));
    p2: assert (c);
  end
endmodule
