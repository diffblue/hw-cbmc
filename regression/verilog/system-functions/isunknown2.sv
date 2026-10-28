// $isunknown(e) is 1'b1 if $countbits(e, 'x, 'z) != 0, and 1'b0
// otherwise (IEEE 1800-2017 20.9). The cases that EBMC supports.
module main(input clk);
  // constants, and operators applied to constants
  p0: assert final ($isunknown(4'b0000) == 0);
  p1: assert final ($isunknown(4'b1x00) == 1 && $isunknown(4'b10z0) == 1);
  p2: assert final ($bits($isunknown(4'bx)) == 1);
  p3: assert final ($isunknown(4'b1x00 + 4'd1) == 1);
  p4: assert final ($isunknown(4'b1x00 & 4'b0000) == 0);
  p5: assert final ($isunknown(1'bx == 1'b0) == 1);
  p6: assert final ($isunknown(1'bx === 1'b0) == 0);

  // a two-state variable never holds x or z; x and z are converted to 0
  bit [3:0] b = 4'b1x00;
  // a four-state variable holding a known value
  logic [3:0] k = 4'b1010;

  always @(posedge clk) begin
    b <= b;
    k <= k;
  end

  p7: assert property (@(posedge clk) $isunknown(b) == 0 && b == 4'b1000);
  p8: assert property (@(posedge clk) $isunknown(k) == 0);
endmodule
