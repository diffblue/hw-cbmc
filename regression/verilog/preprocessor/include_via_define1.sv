// A `define may expand to an `include directive, with the file name
// passed as a macro argument (1800-2017 22.4).
`define DO_INCLUDE(FN) `include FN

module top ();
  // Multiple expansions on one line must be included in order.
  `DO_INCLUDE("include_via_define1_a.svh") `DO_INCLUDE("include_via_define1_b.svh")

  // An expansion in an inactive branch must not include anything.
  `ifdef NEVER
   `DO_INCLUDE("nonexistent.svh")
  `endif
endmodule
