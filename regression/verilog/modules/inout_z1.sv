// A module drives its inout port with z or with a value, as a tri-state
// buffer does. Where the port is driven with z, the net that it is
// connected to has the value of the other driver (1800-2017 6.6.1).
module buffer(input en, inout [7:0] data);
  assign data = en ? 8'd200 : 8'bz;

  // with the buffer disabled, the value of data is that of the other
  // driver
  p0: assert final (en || data == 100);
endmodule

module main(input [3:0] x);
  wire [7:0] data0, data1;

  buffer b0(1'b1, data0);
  buffer b1(1'b0, data1);

  assign data1 = 100;

  p1: assert final (data0 == 200);
  p2: assert final (data1 == 100);

  // x is not constrained
  p3: assert final (x == 0);
endmodule
