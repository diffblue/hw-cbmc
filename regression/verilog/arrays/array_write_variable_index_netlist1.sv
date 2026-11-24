module main(input clk, input push, input [3:0] idx, input [7:0] d);

  // An unpacked array, written with a variable index
  reg [7:0] q [0:15];
  integer k;

  always @(posedge clk) begin
    for(k = 0; k < 16; k = k + 1)
      q[k] = 0;
    if(push)
      q[idx] = d;
  end

  reg last_push;
  reg [3:0] last_idx;
  reg [7:0] last_d;

  initial last_push = 0;

  always @(posedge clk) begin
    last_push <= push;
    last_idx <= idx;
    last_d <= d;
  end

  p0: assert property (last_push -> q[last_idx] == last_d);

endmodule
