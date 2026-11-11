// Category: SRAM/memory macro (external hard IP)
// Error: "module not found" for memory array wrapper
// Cause: Design instantiates technology-specific SRAM macros
// (e.g., data_arrays_0_ext, tag_array_ext) that are provided
// by the foundry/memory compiler, not defined in RTL.
// Fix: provide a behavioral model or stub for SRAM macros,
// or estimate memory area separately (bits × density).

module sram_example(input clk, input [5:0] addr, input [31:0] wdata,
                    input we, output reg [31:0] rdata);
  // In real Chisel output this would be:
  //   sram_64x32_ext sram_inst(.addr(...), .rdata(...), ...);
  // which is undefined in RTL
  reg [31:0] mem [0:63];
  always @(posedge clk) begin
    if (we) mem[addr] <= wdata;
    rdata <= mem[addr];
  end
endmodule
