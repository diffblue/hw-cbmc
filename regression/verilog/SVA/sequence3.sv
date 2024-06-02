module main;

  reg [31:0] x;
  wire clk;

  initial x=0;

  always @(posedge clk)
    if(x < 5)
      x<=x+1;

  initial p0: assert property (##[*] x==6); // same as [0:$]
  initial p1: assert property (##[+] x==0); // same as [1:$]

endmodule
