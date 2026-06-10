module main(input clk, input some_input);
  reg [31:0] some_data;
  always @(posedge clk) some_data = some_other_data;
  wire [31:0] some_other_data = some_data + some_input;
endmodule
