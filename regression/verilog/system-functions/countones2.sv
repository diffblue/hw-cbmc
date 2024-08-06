module gray_counter#(N = 4) (input clk, output [N-1:0] out);

  reg [N-1:0] state = 0;
  assign out = {state[N-1], state[N-1:1] ^ state[N-2:0]};

  always_ff @(posedge clk) state++;

  // two successive values differ in one bit exactly
  p0: assert property (@(posedge clk)
       ##1 $countones($past(out) ^ out) == 1);

endmodule
