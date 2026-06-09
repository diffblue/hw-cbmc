// state-less
function [31:0] some_func(input [31:0] data_in);
  reg [31:0] data;
  data = data_in + 1;
  return data;
endfunction

module main(input clk, input x);

  // all stateless, hence CT=0
  wire [31:0] out = some_func(x);

  a0: assume property (@(posedge clk) x == 0);
  p0: assert property (@(posedge clk) out == 1);

endmodule
