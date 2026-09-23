module main(input clk, input [2:0] i);

  // Vectors whose range does not start at zero, or is increasing.
  reg [11:4] v1;
  reg [0:7] v2;

  initial begin
    v1 = 0;
    v2 = 0;
  end

  always @(posedge clk) begin
    v1[i + 4] = 1;
    v2[i] = 1;
  end

  p0: assert property (@(posedge clk) ##1 v1[$past(i) + 4] == 1);
  p1: assert property (@(posedge clk) ##1 v2[$past(i)] == 1);

endmodule
