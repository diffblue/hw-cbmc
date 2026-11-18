module main;
`ifdef VALUE
  `macro_survived_undefineall
`endif
`ifdef REMOVE_FROM_COMMAND_LINE
  `command_line_macro_was_reintroduced
`endif
`ifdef KEEP_FROM_COMMAND_LINE
  `macro_survived_undefineall
`endif
  p0: assert property (seen::BEFORE_UNDEFINE == values::EXPECTED);
endmodule
