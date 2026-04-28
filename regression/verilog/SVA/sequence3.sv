module main;

  reg [31:0] x;
  wire clk;

  initial x=0;

  always @(posedge clk)
    if(x < 5)
      x<=x+1;

  // ##[*] is the same as [0:$]
  initial ps0: assert property (strong(##[*] x==6)); // no match
  initial ps1: assert property (strong(##[*] x==5)); // match

  // ##[+] is the same as [1:$]
  initial ps2: assert property (strong(##[+] x==0)); // no match
  initial ps3: assert property (strong(##[+] x==5)); // match

  // ##[*] is the same as [0:$]
  initial pw0: assert property (weak(##[*] x==6)); // no match
  initial pw1: assert property (weak(##[*] x==5)); // match

  // ##[+] is the same as [1:$]
  initial pw2: assert property (weak(##[+] x==0)); // no match
  initial pw3: assert property (weak(##[+] x==5)); // match

  // cover: no witness found (pending matches dropped for cover)
  initial cs0: cover property (strong(##[*] x==6));
  initial cs2: cover property (strong(##[+] x==0));

endmodule
