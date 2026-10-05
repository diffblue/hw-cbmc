// while statement in a procedural (always) block, IEEE 1800-2017 12.7.4.
// When the loop condition is an elaboration-time constant the loop should be
// unrolled during RTL construction, just like a for loop. Here the body runs
// exactly three times, so x becomes 3.
//
// KNOWNBUG: verilog_rtl_buildert::build_statement in
// src/verilog/verilog_rtl.cpp has no case for ID_while and reports
// "statement `while' is not supported by RTL construction" (CONVERSION ERROR).
module main(input clk);
  reg [7:0] x;
  always @(posedge clk) begin
    integer i;
    x = 0;
    i = 0;
    while (i < 3) begin x = x + 1; i = i + 1; end
  end
  p0: assert property (@(posedge clk) ##1 x == 3);
endmodule
