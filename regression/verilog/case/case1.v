module main(input clk, x, y);

  reg [1:0] cnt1;
  reg result;
  
  initial cnt1=0;
  initial result=0;
  
  always @(posedge clk) cnt1=cnt1+1;

  always @(posedge clk)
    casex (cnt1)
      2'b00:;
      2'b01:;
      2'b1?: result=1;
    endcase
    
  always assert p1: result==0;

endmodule
