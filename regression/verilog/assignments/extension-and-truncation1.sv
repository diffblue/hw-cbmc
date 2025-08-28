module converter(input signed [7:0] si, input unsigned [7:0] ui);

  // 1800-2017 10.7 Assignment extension and truncation

  // enlarge
  // The RHS is padded or sign extended.
  wire signed [31:0] sw1 = ui;   // unsigned 8 to signed 32
  wire signed [31:0] sw2 = si;   // signed 8 to signed 32
  wire unsigned [31:0] uw1 = ui; // unsigned 8 to unsigned 32
  wire unsigned [31:0] uw2 = si; // signed 8 to unsigned 32

  // shrink
  // The RHS is truncated.
  // Icarus Verilog yields 'z' for this, but the standard requires
  // truncation.  VCS, Questa, Xcelium, Riviera implement this.
  wire signed [3:0] sn1 = ui;   // unsigned 8 to signed 4
  wire signed [3:0] sn2 = si;   // signed 8 to signed 4
  wire unsigned [3:0] un1 = ui; // unsigned 8 to unsigned 4
  wire unsigned [3:0] un2 = si; // signed 8 to unsigned 4

  // same size
  wire signed [7:0] sb1 = ui;   // unsigned 8 to signed 8
  wire signed [7:0] sb2 = si;   // signed 8 to signed 8
  wire unsigned [7:0] ub1 = ui; // unsigned 8 to unsigned 8
  wire unsigned [7:0] ub2 = si; // signed 8 to unsigned 8

  // just one bit
  wire signed sbit1 = ui;       // unsigned 8 to signed 1
  wire signed sbit2 = si;       // signed 8 to signed 1
  wire unsigned ubit1 = ui;     // unsigned 8 to unsigned 1
  wire unsigned ubit2 = si;     // signed 8 to unsigned 1

endmodule

module main;

  converter c(8'sb1000_1000, 8'b1000_1000);

  assert final(c.sw1 == 136);
  assert final(c.sw2 == -120);
  assert final(c.uw1 == 136);
  assert final(c.uw2 == 4294967176);
  assert final(c.sn1 == -8);
  assert final(c.sn2 == -8);
  assert final(c.un1 == 8);
  assert final(c.un2 == 8);
  assert final(c.sb1 == -120);
  assert final(c.sb2 == -120);
  assert final(c.ub1 == 136);
  assert final(c.ub2 == 136);
  assert final(c.sbit1 == 0);
  assert final(c.sbit2 == 0);
  assert final(c.ubit1 == 0);
  assert final(c.ubit2 == 0);

  initial begin
    $display("c.sw1 == ", c.sw1);
    $display("c.sw2 == ", c.sw2);
    $display("c.uw1 == ", c.uw1);
    $display("c.uw2 == ", c.uw2);

    $display("c.sn1 == ", c.sn1);
    $display("c.sn2 == ", c.sn2);
    $display("c.un1 == ", c.un1);
    $display("c.un2 == ", c.un2);

    $display("c.sb1 == ", c.sb1);
    $display("c.sb2 == ", c.sb2);
    $display("c.ub1 == ", c.ub1);
    $display("c.ub2 == ", c.ub2);

    $display("c.sbit1 == ", c.sbit1);
    $display("c.sbit2 == ", c.sbit2);
    $display("c.ubit1 == ", c.ubit1);
    $display("c.ubit2 == ", c.ubit2);
  end

endmodule
