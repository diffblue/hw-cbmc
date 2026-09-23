module main(input clk, input [1:0] i);

  // An array whose range does not start at zero.
  reg [7:0] a [4:7];

  initial begin
    a[4] = 0;
    a[5] = 0;
    a[6] = 0;
    a[7] = 0;
  end

  always @(posedge clk)
    a[i + 4] = 8'h11;

  p0: assert property (@(posedge clk) ##1 a[$past(i) + 4] == 8'h11);

endmodule
