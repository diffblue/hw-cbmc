module main(input clk, input [2:0] i);

  reg [7:0] v;

  initial v = 0;

  always @(posedge clk) begin
    // a blocking assignment to a constant part of v
    v[7:4] = 4'hF;
    // followed by a blocking assignment with a non-constant index
    v[i] = 1'b1;
  end

  p0: assert property (@(posedge clk) ##1 v[7:4] == 4'hF);

endmodule
