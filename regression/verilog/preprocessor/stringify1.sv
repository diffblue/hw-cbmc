// `" inside a macro body stands for a double quote whose contents
// undergo macro-argument substitution and macro expansion; `\`" stands
// for an escaped double quote (IEEE 1800-2017 22.5.1).
// Reduced from the UVM library (uvm_object_defines.svh).
`define str(S) `"S`"
`define phase(P, Q) `"P``Q``_phase`"
`define FOO bar
`define embedded(X) `"X `FOO`"
`define escaped(X) `"X `\`"q`\`"`"

module main;
  p0: assert final (`str(abc) == "abc");
  p1: assert final (`phase(run, x) == "runx_phase");
  p2: assert final (`embedded(a) == "a bar");
  p3: assert final (`escaped(z) == "z \"q\"");
  p4: assert final (`str(a + b) == "a + b");
  // not in a macro body
  p5: assert final ("S`" == "S`");
endmodule
