// Path conditions of break and continue statements, IEEE 1800-2017 12.8.
module main(input clk, input c, input d);
  reg [3:0] x = 0;
  reg [3:0] y = 0;
  reg [3:0] z = 0;
  reg [3:0] w = 0;

  always @(posedge clk) begin
    // continue: the rest of the body is only reached when !c
    x = 0;
    for (int i = 0; i < 3; i++) begin
      if (c) continue;
      p0: assert (!c);
      x = x + 1;
    end
    p1: assert (x == (c ? 0 : 3));

    // two conditional breaks: the second is only reached when !c
    y = 0;
    for (int i = 0; i < 3; i++) begin
      if (c) break;
      p2: assert (!c);
      if (d) break;
      p3: assert (!c && !d);
      y = y + 1;
    end
    p4: assert (y == ((c || d) ? 0 : 3));

    // nested loops: break leaves the inner loop only
    z = 0;
    w = 0;
    for (int i = 0; i < 2; i++) begin
      for (int j = 0; j < 3; j++) begin
        if (c) break;
        z = z + 1;
      end
      w = w + 1;
    end
    p5: assert (w == 2);
    p6: assert (z == (c ? 0 : 6));

    // break under a constant condition leaves the loop; the rest
    // of the always block is reachable
    for (int i = 0; i < 3; i++) begin
      if (i == 1) break;
      p7: assert (i == 0);
    end
    p8: assert (1);
    p9: assert (c);
  end
endmodule
