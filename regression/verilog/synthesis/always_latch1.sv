// always_latch (IEEE 1800-2017 9.2.2.3) describes a level-sensitive latch:
// the variable follows its data input while the enable is active, and holds
// its previous value otherwise. Here q = d while en is high; when en is low q
// retains its value. The assertion only observes q while en is high, so q must
// equal d and the property is expected to be PROVED.
//
// EBMC currently rejects the construct outright: verilog_rtl_buildert::build_always
// in src/verilog/verilog_rtl.cpp throws
// "always_latch is not supported by RTL construction", so this is a KNOWNBUG.
module main(input clk, input en, input [3:0] d);

  reg [3:0] q;

  always_latch if (en) q = d;

  p0: assert property (@(posedge clk) en |-> q == d);

endmodule
