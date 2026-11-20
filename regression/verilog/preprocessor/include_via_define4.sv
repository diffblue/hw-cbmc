// White space inside the macro argument parentheses (1800-2017 22.5.1)
// and an argument forwarded through a second macro must both work.
`define DO_INCLUDE(FN) `include FN
`define FWD(F) `DO_INCLUDE(F)

module top ();
  `DO_INCLUDE( "include_via_define1_a.svh" )
  `FWD("include_via_define1_b.svh")
endmodule
