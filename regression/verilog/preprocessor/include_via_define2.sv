// Text following a macro-generated `include on the same line must be
// preserved (and emitted after the included content), not dropped.
`define INC(F) `include F

module top ();
`INC("include_via_define1_a.svh") wire trailing;
endmodule
