module buffer(input i, output o);
  assign o = i;
endmodule

module main(input clk, input [1:0] x);

  genvar g;
  wire [1:0] y, z;

  // Two unnamed generate loops in one module; the second instantiates a
  // module. 1800-2017 27.6 names their blocks genblk1 and genblk2.
  generate
    for(g = 0; g < 2; g = g + 1) begin
      assign y[g] = x[g];
    end
  endgenerate

  for(g = 0; g < 2; g = g + 1) begin
    buffer c(.i(y[g]), .o(z[g]));
  end

  p0: assert property (@(posedge clk) z == x);
  p1: assert property (@(posedge clk) genblk2[1].c.o == x[1]);

endmodule
