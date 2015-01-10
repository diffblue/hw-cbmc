module top(input clock, input valid);

  reg [1:0] e_ctl_reg;
  reg tick;  
  initial tick=0;
  
  always @(posedge clock)
    begin
      e_ctl_reg[1]=0;
      tick=1;
    end

  always @(posedge clock)
    if(valid) begin
      e_ctl_reg[0]=1;
    end

  always assert p1: !tick || e_ctl_reg[1]==0;

endmodule
