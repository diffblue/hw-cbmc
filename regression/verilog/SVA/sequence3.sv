module main;

  reg [31:0] x;
  wire clk;

  initial x=0;

  always @(posedge clk)
    if(x < 5)
      x<=x+1;

  // ##[*] is the same as [0:$]
  initial p0: assert property (##[*] x==6); // should fail
  initial p1: assert property (##[*] x==5); // should pass

  // ##[+] is the same as [1:$]
  initial p2: assert property (##[+] x==0); // should fail
  initial p3: assert property (##[+] x==5); // should pass

endmodule
