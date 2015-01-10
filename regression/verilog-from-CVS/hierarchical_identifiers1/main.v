module M ();
  reg [31:0] out;
  wire x;

  always @x out=-1;

endmodule

module main;
  wire [31:0] bin;

  assign bin=m.out;

  M m();
  
  always assert property1: bin=='hffffffff;
  
endmodule
