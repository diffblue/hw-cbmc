module main(input clk);

  reg [7:0] a [0:1];
  reg [7:0] r;
  reg [0:0] i;

  initial begin
    a[0] = 10;
    a[1] = 20;
    r = 0;
    i = 1;
  end

  always @(posedge clk) begin
    // A nonblocking assignment to a[0]. Its update commits only in
    // the NBA region (1800-2017 4.9.3), so it is not visible to the
    // blocking assignments and reads that follow in this block.
    a[0] <= 99;
    // A blocking assignment with a non-constant index. With i == 1
    // this touches a[1] only; the with-rewrite takes the OLD value
    // of a from the blocking-assignment values, leaving a[0] == 10,
    // rather than the nonblocking-scheduled 99.
    a[i] = 7;
    // A blocking read: observes the OLD a[0] == 10, not 99, and not
    // the nonblocking-scheduled value.
    r = a[0];
  end

  // The blocking read sees the old a[0] == 10 (not the nonblocking 99).
  p0: assert property (@(posedge clk) ##1 r == 10);
  // The blocking assignment with a non-constant index leaves a[0]
  // untouched, so the old blocking value 10 is preserved.
  p1: assert property (@(posedge clk) ##1 a[1] == 7);

endmodule
