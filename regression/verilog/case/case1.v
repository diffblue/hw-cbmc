module main(input clk, x, y);

  reg [1:0] cnt1;
  reg z;
  
  initial cnt1=0;
  initial z=0;
  
  always @(posedge clk) cnt1=cnt1+1;

  always @(posedge clk)
    casex (cnt1)
      2'b00:;
      2'b01:;
      2'b1?: z=1;
    endcase
    
  always assert p1: z==0;

endmodule
