// A repeated `define must replace the previous definition, not append to
// it (IEEE 1800-2017 22.5.1). Reduced from LogikBench large/nvdlafull and
// large/nvdlasmall, where FORCE_CONTENTION_ASSERTION_RESET_ACTIVE is
// defined as 1'b1 several times in the same file; appending turned the
// expansion into "1'b11'b1".
`define FORCE 1'b1
`define FORCE 1'b1
module sub #(parameter P = 0) (input a); endmodule
module main(input a);
  sub #(`FORCE) u (.a(a));
endmodule
