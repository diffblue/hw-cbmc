module m(input c1, c2, c3, output reg [31:0] x);

  // this is a kind of priority encoder
  always @(*)
    casex(1'b1)
      c1: x=1;
      c2: x=2;
      c3: x=3;
      default: x=0;
    endcase

endmodule

module main();

  wire [31:0] x;
  wire c1, c2, c3;

  m m(c1, c2, c3, x);

  always assert p1:
    !c1 || 
    (c1?x==1:
    c2?x==2:
    c3?x==3:
    x==0);

endmodule
