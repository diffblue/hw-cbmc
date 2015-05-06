module m;

  wire clock;

  always @(posedge clock) begin : my_block
    reg [31:0] x;
    if(x==10)
      x=1;
    else
      x=x+1;
  end
  
  initial my_block.x=1;
  
  always assert p1: my_block.x>=1 && my_block.x<=10;

endmodule
