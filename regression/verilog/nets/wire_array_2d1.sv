// A two-dimensional unpacked array of nets, assigned element-wise in
// terms of other elements.
module main(input clk, input [1:0] x);
  wire [1:0] arr [0:1][0:1];
  assign arr[0][0] = x;
  assign arr[0][1] = arr[0][0] + 2'd1;
  assign arr[1][0] = arr[0][1] + 2'd1;
  assign arr[1][1] = arr[1][0] - arr[0][0];
  p0: assert property (@(posedge clk) arr[1][1] == 2'd2);
  p1: assert property (@(posedge clk) arr[1][1] == 2'd0); // fails
endmodule
