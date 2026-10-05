// An assertion that follows a conditional `break` inside a loop body is
// only reached when the break was NOT taken, so its path condition must
// include the negation of the break's condition (IEEE 1800-2017,
// section 12.8 "Jump statements": `break` terminates the loop, so any
// statement after `if (c) break;` executes only when `c` is false).
//
// Here `if (c) break; p0: assert(!c);` means p0 is only reached when
// `!c`, so the assertion can never fail and must be PROVED.
//
// KNOWNBUG: in verilog_rtl_buildert (src/verilog/verilog_rtl.cpp) `break`
// pushes false_exprt onto the guard of the taken branch, but when the `if`
// condition is non-constant the two branches are combined with merge(),
// which only merges the value maps and discards the branch guards. The
// break's path condition (!c) is therefore lost for the remainder of the
// loop body, so p0 is checked without the `!c` guard and is spuriously
// REFUTED.
module main(input clk, input c);
  reg [3:0] x = 0;
  always @(posedge clk) begin
    for (int i = 0; i < 2; i++) begin
      if (c) break;
      p0: assert (!c); // only reached when !c -> must be PROVED
    end
  end
endmodule
