module PWM_TOP (input clk, input [3:0] sw, output reg pulse_red, output reg lb_pulse, output reg ub_pulse);

  localparam CBITS = 18;    // Change pulse_wideR accordingly
  
  wire [CBITS-1:0] pulse_wideR;
  assign pulse_wideR = {1'b0, sw[3:1], 1'b1, 13'd0};     // (CBTIS-5)
  assign lbR = {1'b0, 4'b0000, 1'b1, 13'd0};
  assign ubR = {1'b0, 4'b1111, 1'b1, 13'd0};

  reg [CBITS-1:0] cnt_R;

  always @(posedge clk) begin
    cnt_R <= cnt_R + 1;
    
    if (cnt_R < pulse_wideR)
      pulse_red = 1;
    else
      pulse_red = 0;

    if (cnt_R < lbR)
      lb_pulse = 1;
    else
      lb_pulse = 0;
    
    if (cnt_R < ubR)
      ub_pulse = 1;
    else
      ub_pulse = 0;
  end


  // LTLSPEC X G ((Verilog.PWM_TOP.lb_pulse = TRUE -> Verilog.PWM_TOP.pulse_red = TRUE) & (Verilog.PWM_TOP.ub_pulse = FALSE -> Verilog.PWM_TOP.pulse_red = FALSE))
  assert property (@(posedge clk) ##1 ((lb_pulse -> pulse_red) && (!ub_pulse -> !pulse_red)));

endmodule