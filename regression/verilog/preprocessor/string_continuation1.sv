// A string literal in a macro argument may be continued on the next
// line with a backslash (IEEE 1800-2017 5.9); a comma after the line
// continuation is part of the string, not an argument separator.
// Reduced from the UVM library (uvm_reg_map.svh).
`define m(a, b) a + b

module main;
  initial $display(`m("x \
y,z", 1));
endmodule
