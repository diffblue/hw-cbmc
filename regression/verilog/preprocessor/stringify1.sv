// `" inside a macro body stands for a double quote whose contents
// undergo macro-argument substitution (IEEE 1800-2017 22.5.1).
// Reduced from the UVM library (uvm_object_defines.svh).
`define str(S) `"S`"

module main;
  p0: assert final (`str(abc) == "abc");
endmodule
