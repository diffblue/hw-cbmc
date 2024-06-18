module main(input clk, x, y);

  reg [1:0] cnt1;
  reg out;
  
  initial cnt1=0;
  initial out=0;
  
  always @(posedge clk) 
    if(cnt1==0)
      cnt1=1;
    else if(cnt1==1)
      cnt1=3;

  always @(posedge clk)
    casez (cnt1)
      10'b0z00:;
      10'b0z01:;
      10'b0z1z: out=1;
    endcase
    
  always assert p1: out==0;

endmodule
