module main;

  reg [31:0] x;
  wire clk;

  initial x=0;

  always @(posedge clk)
    if(x < 5)
      x<=x+1;

  // Should pass
  initial p0: assert property (x==0 ##[*] x==0);
  initial p1: assert property (x==0 ##[*] x==1);
  initial p2: assert property (x==0 ##[*] x==2);

  // Should fail
  initial p3: assert property (x==1 ##[*] x==1);

  // Shoud pass, owing to weak sequence semantics
  initial p4: assert property (x==0 ##[*] x==6);

endmodule
