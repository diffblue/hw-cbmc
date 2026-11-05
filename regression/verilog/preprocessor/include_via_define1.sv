// A `define may expand to an `include directive, with the file name
// passed as a macro argument (1800-2017 22.4).
`define DO_INCLUDE(FN) `include FN

// Multiple expansions on one line must not be rejected.
`DO_INCLUDE("include_via_define1.svh") `DO_INCLUDE("include_via_define1.svh")

// An expansion in an inactive branch must not include anything.
`ifdef NEVER
 `DO_INCLUDE("nonexistent.svh")
`endif

module top ();
endmodule
