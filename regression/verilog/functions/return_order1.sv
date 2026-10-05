// Multiple conditional `return` statements in a function.
// Per IEEE 1800-2017 section 13.4.1, `return` terminates the function
// immediately, so an earlier `return` whose condition holds must take
// priority over any later statement, including a later `return`. Here, if
// `cc` is true the function returns 4'd1 and the second `return 4'd0` must
// never be reached. Hence f(1)==1 and f(0)==0.
//
// KNOWNBUG: verilog_rtl_buildert::expand_function_call /
// build_function_call in src/verilog/verilog_rtl.cpp merge the recorded
// `return_states` in forward program order, so the later unconditional
// `return 4'd0` overrides the earlier conditional `return 4'd1`. As a
// result f(1) wrongly evaluates to 0 and p0 is REFUTED. Compare the
// correct, reverse-order merge used for `break_states` in build_for.
module main(input clk, input c);

  function automatic [3:0] f(input cc);
    if (cc) return 4'd1;
    return 4'd0;
  endfunction

  reg [3:0] y;
  always @(posedge clk) y <= f(c);

  p0: assert property (@(posedge clk) c |-> ##1 y == 1);  // must be PROVED
  p1: assert property (@(posedge clk) !c |-> ##1 y == 0); // must be PROVED

endmodule
