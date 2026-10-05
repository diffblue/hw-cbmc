// A for loop with a constant-true loop guard that is exited solely via a
// `break` must terminate during RTL construction once the break is taken
// (IEEE 1800-2017, section 12.8 "Jump statements": `break` terminates the
// loop). Here the loop body executes three times (i = 0,1,2) and breaks at
// i == 3, so `count` ends at 3 and `p0: assert(r == 3)` must be PROVED.
//
// KNOWNBUG: in verilog_rtl_buildert::build_for (src/verilog/verilog_rtl.cpp)
// `break` kills the path by pushing false_exprt onto state.guard, but
// build_for keeps unrolling as long as the (constant) loop guard is true
// and does not stop when the path is dead. With the loop guard constant
// `1`, build_for never terminates and ebmc hangs instead of exiting the
// loop at the break.
module main(input clk);
  reg [3:0] r = 0;
  always @(posedge clk) begin
    int count;
    count = 0;
    for (int i = 0; 1; i++) begin
      if (i == 3) break;
      count = count + 1;
    end
    r = count;
    p0: assert (r == 3); // loop exits via break -> must terminate and PROVE
  end
endmodule
