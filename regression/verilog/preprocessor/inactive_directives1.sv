`ifdef NOT_DEFINED
`__FILE__
`__LINE__
`default_nettype none
`endif

`default_nettype wire
module main;
  localparam int LINE = `__LINE__;
  localparam string FILE = `__FILE__;
endmodule
