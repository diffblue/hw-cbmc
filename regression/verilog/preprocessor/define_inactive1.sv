// A `define in an inactive `ifdef branch whose macro text is continued
// on the next lines. The continued lines are part of the ignored macro
// text, and are not processed (reduced from the UVM library,
// uvm_object_defines.svh).
`ifdef NOT_DEFINED
`define m(T) \
  `"T`" \
  `error_not_a_directive
`endif

module main;
  p0: assert final (1);
endmodule
