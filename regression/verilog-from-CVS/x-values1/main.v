module main;

  wire [7:0] in;

  wire [2:0] out = 
    (in == 8'b0000000x) ? 3'b000 :3'b001;

  always assert property1:
    (in[0]>>1) ? out==0 : out==1 ;

endmodule
