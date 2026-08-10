// Commas nested inside (), [] or {} within a single macro argument
// must not be counted as argument separators (IEEE 1800-2017 22.5.1).
// Reduced from LogikBench blocks/picorv32.
`define debug(debug_command) debug_command

module main(input clk);
  integer a, b;
  always @(posedge clk) begin
    `debug($display("LD_RS2: %2d 0x%08x", a, b);)
    a <= b + 1;
  end
endmodule
