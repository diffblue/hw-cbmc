module main;

  reg [31:0] x;
  wire clk;

  initial x=0;

  always @(posedge clk)
    if(x < 5)
      x<=x+1;

  // ##[*] is the same as [0:$]
  initial p0: assert property (strong(##[*] x==6)); // no match
  initial p1: assert property (strong(##[*] x==5)); // match

  // ##[+] is the same as [1:$]
  initial p2: assert property (strong(##[+] x==0)); // no match
  initial p3: assert property (strong(##[+] x==5)); // match

endmodule
