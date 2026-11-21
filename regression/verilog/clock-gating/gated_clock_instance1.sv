// an integrated clock gating cell
module icg(input CK, input EN, output Q);
  assign Q = CK & EN;
endmodule

module main(input clk, input en, input [7:0] d, output reg [7:0] q, output reg r);
  wire gclk;

  icg u0(.CK(clk), .EN(en), .Q(gclk));

  always @(posedge gclk) begin
    q[3:0] <= d[3:0];
    if(d[7])
      q[7:4] <= d[7:4];
  end

  always @(posedge clk) r <= d[0];

  p_hold: assert property (!en |=> $stable(q));
  p_low: assert property (en |=> q[3:0] == $past(d[3:0]));
  p_high: assert property (en && d[7] |=> q[7:4] == $past(d[7:4]));
  p_high_hold: assert property (!d[7] |=> $stable(q[7:4]));
endmodule
