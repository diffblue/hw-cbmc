`include "compilation_unit_macros1_header.svh"

`ifdef REMOVE_FROM_COMMAND_LINE
  `command_line_macro_was_reintroduced
`endif

`ifndef KEEP_FROM_COMMAND_LINE
  `command_line_macro_was_lost
`endif

package seen;
  localparam int BEFORE_UNDEFINE = `VALUE;
endpackage

`undefineall
