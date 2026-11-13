// A macro-generated `include with a quoted file name must be resolved
// relative to the including file, even when ebmc is run from another
// directory.
`define INC(F) `include F

module top ();
`INC("include_file.vh")
endmodule
