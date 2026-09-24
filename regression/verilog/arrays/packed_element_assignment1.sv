module main(input clk);

  // In a packed array, the element with the left index is
  // the most significant.
  logic [1:0][3:0] a1;
  logic [0:1][3:0] a2;

  // Packed arrays with a non-zero offset.
  logic [5:4][3:0] a3;
  logic [4:5][3:0] a4;

  initial begin
    a1 = 0;
    a2 = 0;
    a3 = 0;
    a4 = 0;
  end

  always @(posedge clk) begin
    a1[1] = 4'hA;
    a1[0] = 4'h5;
    a2[0] = 4'hA;
    a2[1] = 4'h5;
    a3[5] = 4'hA;
    a3[4] = 4'h5;
    a4[4] = 4'hA;
    a4[5] = 4'h5;
  end

  p0: assert property (@(posedge clk) ##1 a1 == 8'hA5);
  p1: assert property (@(posedge clk) ##1 a2 == 8'hA5);
  p2: assert property (@(posedge clk) ##1 a1[1] == 4'hA);
  p3: assert property (@(posedge clk) ##1 a2[0] == 4'hA);
  p4: assert property (@(posedge clk) ##1 a3 == 8'hA5);
  p5: assert property (@(posedge clk) ##1 a4 == 8'hA5);

endmodule
