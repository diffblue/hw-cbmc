// A shared loop counter declared with the SystemVerilog 'int' type (not
// the Verilog 'integer' type) exposes a gap in the shared-loop-counter
// driver-conflict exemption: the exemption in verilog_rtl_buildert::commit
// keys on ID_C_verilog_type == ID_integer, so an 'int' (or 'reg'/'logic')
// loop index shared by two blocks is still wrongly rejected as a driver
// conflict. The right criterion is liveness (the index is dead outside the
// loop), not the declared type -- cf. Icarus Verilog bug #1000 and Yosys,
// which both discriminate on usage, not type.
// Desired behaviour: PROVED (same as shared-loop-variable2.sv with 'integer').
module main(input [3:0] din, output reg [3:0] a, output reg [3:0] b);

  int i;

  always @(*)
    for (i = 0; i < 4; i = i + 1)
      a[i] = din[i];

  always @(*)
    for (i = 0; i < 4; i = i + 1)
      b[i] = din[i];

  p0: assert final (a == b);

endmodule
