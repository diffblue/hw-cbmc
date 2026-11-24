module main(input clk, input push, input [3:0] idx);

  // An unpacked array of 1-bit variables, written with a variable index
  reg q [0:15];
  integer k;

  always @(posedge clk) begin
    for(k = 0; k < 16; k = k + 1)
      q[k] = 1'b0;
    if(push)
      q[idx] = 1'b1;
  end

  reg last_push;
  reg [3:0] last_idx;

  initial last_push = 0;

  always @(posedge clk) begin
    last_push <= push;
    last_idx <= idx;
  end

  p0: assert property (last_push -> q[last_idx]);

endmodule
