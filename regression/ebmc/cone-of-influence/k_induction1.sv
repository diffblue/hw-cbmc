module main(input clk, input [7:0] in1);

  reg [7:0] x;
  reg [31:0] unrelated;

  initial x = 0;
  initial unrelated = 0;

  always @(posedge clk) begin
    x <= x | 8'h01;
    unrelated <= unrelated * in1;
  end

  // inductive: once set, bit 0 stays set
  p0: assert property (x[0] == 1 || x == 0);

endmodule
