module main;
  reg [31:0] bin;
  wire x;

  always @x bin[1]=1;
  always @x bin[2]=1;
  
  always assert property1: (bin&6)==6;

endmodule
