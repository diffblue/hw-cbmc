// A byte-enabled memory write: an indexed part-select ([off +: width]) as
// the lvalue of an assignment to an array element. This is a common
// memory-write idiom (a[addr][bit +: width] <= data), and is accepted as
// an lvalue for a plain vector (assignment-to-indexed-part-select1.sv),
// but verilog_rtl_buildert::lower_lhs does not lower it when the base of
// the part-select is itself an array element.
// Regression for LogikBench blocks/axiram and memory/rambyte, large/lz77
// (lambdalib la_spram_impl.v).
module main(
  input clk, input we, input [1:0] addr, input [3:0] wdata,
  output [3:0] rdata);

  reg [3:0] mem [0:3];

  always @(posedge clk)
    if(we)
      mem[addr][2 +: 2] <= wdata[2 +: 2];

  assign rdata = mem[addr];

endmodule
