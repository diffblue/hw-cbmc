module converter(input signed [7:0] si, input unsigned [7:0] ui);

  // enlarge
  wire signed [31:0] sw1 = ui;   // unsigned 8 to signed 32
  wire signed [31:0] sw2 = si;   // signed 8 to signed 32
  wire unsigned [31:0] uw1 = ui; // unsigned 8 to unsigned 32
  wire unsigned [31:0] uw2 = si; // signed 8 to unsigned 32

  // shrink
  wire signed [3:0] sn1 = ui;   // unsigned 8 to signed 4
  wire signed [3:0] sn2 = si;   // signed 8 to signed 4
  wire unsigned [3:0] un1 = ui; // unsigned 8 to unsigned 4
  wire unsigned [3:0] un2 = si; // signed 8 to unsigned 4

  // same size
  wire signed [7:0] sb1 = ui;   // unsigned 8 to signed 8
  wire signed [7:0] sb2 = si;   // signed 8 to signed 8
  wire unsigned [7:0] ub1 = ui; // unsigned 8 to unsigned 8
  wire unsigned [7:0] ub2 = si; // signed 8 to unsigned 8

endmodule

module main;

  converter c(8'sb1000_0000, 8'b1000_0000);

  assert final(c.sw1 == 128);
  assert final(c.sw2 == -128);
  assert final(c.uw1 == 128);
  assert final(c.uw2 == 4294967168);
  assert final(c.sn1 == 'z);
  assert final(c.sn2 == 'z);
  assert final(c.un1 == 'z);
  assert final(c.un2 == 'z);
  assert final(c.sb1 == -128);
  assert final(c.sb2 == -128);
  assert final(c.ub1 == 128);
  assert final(c.ub2 == 128);

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
  end

endmodule
