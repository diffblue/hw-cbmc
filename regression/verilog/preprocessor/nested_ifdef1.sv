// A nested `ifdef that appears "inline", i.e., on the same line as an
// enclosing `ifdef that evaluates to FALSE. Both conditionals are closed
// by the two `endif on the same line, so the conditional nesting returns
// to depth zero and the code following the block must be emitted.
`ifdef NOT_DEFINED `ifdef ALSO_NOT_DEFINED `endif `endif
module main;
endmodule
