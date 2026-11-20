module main(input [3:0] a);

  wire [3:0] x, y;
  genvar i;

  // Unnamed generate blocks are named genblk1, genblk2, ...
  // (1800-2017 27.6), so the two declarations of t do not clash.
  for(i = 0; i < 4; i = i + 1) begin
    wire t = a[i];
    assign x[i] = t;
  end

  for(i = 0; i < 4; i = i + 1) begin
    wire t = ~a[i];
    assign y[i] = t;
  end

  p0: assert property (x == ~y);

endmodule
