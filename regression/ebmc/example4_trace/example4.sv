module counter(
  output [7:0] out,
  input reset, input clk);

  reg [7:0] state;
  assign out = state;

  always @(posedge clk)
    if(reset)
      state = 0;
    else
      state = state + 1;

  assert property (reset |-> ##1 state==0);
  assert property (reset |-> ##2 state==1);

endmodule
