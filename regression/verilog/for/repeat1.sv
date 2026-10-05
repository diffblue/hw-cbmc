// repeat statement in a procedural (always) block, IEEE 1800-2017 12.7.2.
// When the repeat count is an elaboration-time constant the loop should be
// unrolled during RTL construction, just like a for loop. Here the body runs
// exactly three times, so x becomes 3.
//
// KNOWNBUG: verilog_rtl_buildert::build_statement in
// src/verilog/verilog_rtl.cpp has no case for ID_repeat and reports
// "statement `repeat' is not supported by RTL construction" (CONVERSION ERROR).
module main(input clk);
  reg [7:0] x;
  always @(posedge clk) begin
    x = 0;
    repeat (3) x = x + 1;
  end
  p0: assert property (@(posedge clk) ##1 x == 3);
endmodule
