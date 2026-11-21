module main(input clk, input en, input d, output reg q, output reg r);
  wire gclk = clk & en;

  always @(posedge gclk) begin
    q <= d;
    // checked when the gated clock has an edge only
    a1: assert property (en);
  end

  always @(posedge clk) begin
    r <= d;
    // checked in every step
    a2: assert property (en);
  end
endmodule
