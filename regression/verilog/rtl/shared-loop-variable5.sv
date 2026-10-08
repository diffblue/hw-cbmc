// Same gap as shared-loop-variable4.sv, but with the loop index declared
// 'reg [31:0]' rather than 'int'. The driver-conflict exemption keys on
// the 'integer' Verilog type, so a 'reg'-typed loop index is not exempted
// and the benign shared counter is still rejected as a spurious driver
// conflict.
// Desired behaviour: PROVED (same as shared-loop-variable2.sv with 'integer').
module main(input [3:0] din, output reg [3:0] a, output reg [3:0] b);

  reg [31:0] i;

  always @(*)
    for (i = 0; i < 4; i = i + 1)
      a[i] = din[i];

  always @(*)
    for (i = 0; i < 4; i = i + 1)
      b[i] = din[i];

  p0: assert final (a == b);

endmodule
