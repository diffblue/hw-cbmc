module main;

  reg [31:0] val;

  initial val = 100;

  // $value$plusargs returns 0 (not found) in synthesis
  always assert ($value$plusargs("SEED=%d", val) == 0);

endmodule
