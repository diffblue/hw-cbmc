module PWM_TOP (input clk, input [3:0] sw, output reg pulse_red);

  localparam CBITS = 16;    // Change pulse_wideR accordingly
  
  wire [CBITS-1:0] pulse_wideR;
  assign pulse_wideR = {1'b0, sw[3:1], 12'd0};     // (CBTIS-4)

  reg [CBITS-1:0] cnt_R;

  always @(posedge clk) begin
    cnt_R <= cnt_R + 1;
    
    if (cnt_R < pulse_wideR)
      pulse_red = 1'b1;
    else
      pulse_red = 1'b0;
  
  end
  p1: assert property  (@(posedge clk) (always s_eventually pulse_red == 0)) ;
  // G F (pulse = F)
  // G F (pulse = F) is instantaneous for EBMC-BDD but G F (pulse = T) isn't
endmodule
