module PWM_TOP #(localparam CBITS = 14) (input clk, input [3:0] sw, output reg pulse);
  
  wire [CBITS-1:0] pulse_wide;
  assign pulse_wide = {1'b0, sw[3:1], 10'd0};     // (CBTIS-4)

  reg [CBITS-1:0] cntR;

  always @(posedge clk) begin
    cntR <= cntR + 1;
    
    if (cntR < pulse_wide)
      pulse = 1'b1;
    else
      pulse = 1'b0;
  end
  p1: assert property  (@(posedge clk) (always s_eventually pulse == 0)) ;
  // G F (pulse = F)
  // G F (pulse = F) is instantaneous for EBMC-BDD but G F (pulse = T) isn't
endmodule