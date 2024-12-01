module main(input clk);

  reg [31:0] x = 0;

  // 0, 1, 2, 3, 4, 5, 5, ...
  always @(posedge clk)
    if(x<5)
      x<=x+1;

  // should fail
  initial p0: assert property (x == 0 intersect x == 1);

  // should pass
  p1: assert property (x >= 0);

  // should pass
  p2: assert property (x <= 5);

  // should fail
  p3: assert property (x <= 3);

  // should pass
  p4: assert property (x >= 0 intersect x <= 5);

  // should fail
  p5: assert property (x >= 0 intersect x <= 3);

endmodule
