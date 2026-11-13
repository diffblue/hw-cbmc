// An unpacked array whose element 0 is driven by a continuous assignment,
// and whose other elements are driven by the output ports of instances in
// a generate loop. Before 646cc46a ("Word-level BMC: non-deterministic
// values in every time frame"), the undriven bits of the array had the
// same non-deterministic value in every time frame, which conflicted with
// the instance outputs once these changed: no path longer than that
// existed, and p0 was proved.
module dffm(input clk, input din, output reg dout);
  always @(posedge clk) dout <= din;
endmodule

module pipe #(parameter N = 3) (input clk, input din, output dout);
  logic q [N:0];
  assign q[0] = din;
  for(genvar gi = 0; gi < N; gi++) begin : flop
    dffm u(.din(q[gi]), .clk(clk), .dout(q[gi + 1]));
  end
  assign dout = q[N];
endmodule

module main(input clk, input din);
  reg [3:0] t = 0;
  always @(posedge clk) if(t != 4'hF) t <= t + 4'd1;
  wire a;
  pipe #(3) u(.clk(clk), .din(din), .dout(a));

  f1: assume property (@(posedge clk) din == (t != 4'd2));
  // fails: t reaches 8
  p0: assert property (@(posedge clk) !(t == 4'd8));
  // the pipeline has a latency of 3: din is 0 at t == 2 only
  p1: assert property (@(posedge clk) t == 4'd5 -> !a);
  p2: assert property (@(posedge clk) t >= 4'd4 && t != 4'd5 && t != 4'hF -> a);
endmodule
