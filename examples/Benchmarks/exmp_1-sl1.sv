module MODEL (input clk, output reg a, b);
  reg [5:0] c;
  reg b;
  assign a = (c < 50);
  assign b = (c == 50);
  always @(posedge clk) begin
      c <= c + 1; 
  end
    sl1: assert property None;
    // (a U b)
endmodule
