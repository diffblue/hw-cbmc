module top(input wire [3:0] a, input wire s,
           output wire [4:0] y, output wire signed [7:0] w);
  assign y = {s, a};
  assign w = $signed({1'b0, s});
endmodule
