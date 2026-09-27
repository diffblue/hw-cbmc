// A genuine true dual-port RAM: two independent clocked always blocks each
// write the same memory array through a different port. This is
// synthesizable hardware (a well-known IP block, e.g. lambdalib's
// la_tdpram), but ebmc's RTL construction models a memory array with a
// single writer per bit-range across all always blocks, so the second
// write is rejected as a driver conflict rather than modeled as a second
// write port.
// Regression for LogikBench memory/{ramtdp,ramtdpdc} (lambdalib
// la_tdpram_impl.v) and the koios/* circuits that instantiate dual-port
// block RAMs (attention_layer, bwave_like_*, clstm_like_*, conv_layer*,
// dla_like_*, spmv, tpu_like_small_*).
module main(
  input clka, input wea, input [1:0] addra, input [3:0] dina,
  input clkb, input web, input [1:0] addrb, input [3:0] dinb);

  reg [3:0] mem [0:3];

  always @(posedge clka) if(wea) mem[addra] <= dina;
  always @(posedge clkb) if(web) mem[addrb] <= dinb;

endmodule
