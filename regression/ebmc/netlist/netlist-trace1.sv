module counter(
  output [7:0] out,
  input enable, input clk);

  reg [7:0] state;
  assign out = state;

  initial state = 0;

  always @(posedge clk)
    if(enable)
      state = state + 1;

  assert property (state!=3);

endmodule
