`define len 2'b11

module main(clk);
  input clk;
  reg[`len-1:0] c;
  integer i;

  initial
    for(i=0; i <= `len-1; i=i+1) //generics can also be used here
      c[i]=0;
  
  always @(posedge clk)
    c=c;
  
  always assert a1: c==0;

endmodule
