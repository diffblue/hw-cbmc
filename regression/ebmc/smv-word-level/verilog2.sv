module main(input clk, input signed [7:0] si, input unsigned [7:0] ui);

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
