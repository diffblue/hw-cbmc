module main(input clk);

  reg [7:0] x, y;

  initial begin
    x = 0;
    y = 0;
  end

  always @(posedge clk) begin
    // The nonblocking assignment is scheduled in the NBA region,
    // i.e., after the blocking assignment that follows, and hence
    // the value of x after the clock tick is 1.
    x <= 1;
    x = 2;
  end

  always @(posedge clk) begin
    y <= y + 10;
    y++;
  end

  p0: assert property (@(posedge clk) ##1 x == 1);
  p1: assert property (@(posedge clk) ##1 y == $past(y) + 10);

endmodule
