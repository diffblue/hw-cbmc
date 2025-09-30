module main;

`define ui (8'd255+8'd2)
`define si (8'sd127+8'sd1)

  // enlarge
  // The RHS is padded or sign extended.
  wire signed [31:0] sw1 = `ui;   // unsigned 8 to signed 32
  wire signed [31:0] sw2 = `si;   // signed 8 to signed 32
  wire unsigned [31:0] uw1 = `ui; // unsigned 8 to unsigned 32
  wire unsigned [31:0] uw2 = `si; // signed 8 to unsigned 32

  // shrink
  wire signed [3:0] sn1 = `ui;   // unsigned 8 to signed 4
  wire signed [3:0] sn2 = `si;   // signed 8 to signed 4
  wire unsigned [3:0] un1 = `ui; // unsigned 8 to unsigned 4
  wire unsigned [3:0] un2 = `si; // signed 8 to unsigned 4

  // same size
  wire signed [7:0] sb1 = `ui;   // unsigned 8 to signed 8
  wire signed [7:0] sb2 = `si;   // signed 8 to signed 8
  wire unsigned [7:0] ub1 = `ui; // unsigned 8 to unsigned 8
  wire unsigned [7:0] ub2 = `si; // signed 8 to unsigned 8

  // just one bit
  wire signed sbit1 = `ui;       // unsigned 8 to signed 1
  wire signed sbit2 = `si;       // signed 8 to signed 1
  wire unsigned ubit1 = `ui;     // unsigned 8 to unsigned 1
  wire unsigned ubit2 = `si;     // signed 8 to unsigned 1

  assert final(sw1 == 257);
  assert final(sw2 == 128);
  assert final(uw1 == 257);
  assert final(uw2 == 128);
  assert final(sn1 == 1);
  assert final(sn2 == 0);
  assert final(un1 == 1);
  assert final(un2 == 0);
  assert final(sb1 == 1);
  assert final(sb2 == -128);
  assert final(ub1 == 1);
  assert final(ub2 == 128);
  assert final(sbit1 == -1);
  assert final(sbit2 == 0);
  assert final(ubit1 == 1);
  assert final(ubit2 == 0);

  initial begin
    $display("sw1 == ", sw1);
    $display("sw2 == ", sw2);
    $display("uw1 == ", uw1);
    $display("uw2 == ", uw2);

    $display("sn1 == ", sn1);
    $display("sn2 == ", sn2);
    $display("un1 == ", un1);
    $display("un2 == ", un2);

    $display("sb1 == ", sb1);
    $display("sb2 == ", sb2);
    $display("ub1 == ", ub1);
    $display("ub2 == ", ub2);

    $display("sbit1 == ", sbit1);
    $display("sbit2 == ", sbit2);
    $display("ubit1 == ", ubit1);
    $display("ubit2 == ", ubit2);
  end

endmodule
