// The width of an implicitly declared net used in a port connection
// is one bit (IEEE 1800-2017 6.10). When a wider output port drives
// such a net, the value must be truncated to the least-significant
// bit, exactly as a narrowing continuous assignment would.
module sub(input [7:0] din, output [7:0] dout);
  assign dout = din;
endmodule

module main(input [7:0] din);
  // cam is implicitly declared, hence a one-bit scalar net
  sub s(.din(din), .dout(cam));

  // narrowing the 8-bit port to the 1-bit net yields the LSB
  p0: assert property (cam == din[0]);
endmodule
