module M1(input [31:0] in, output reg [31:0] out);

  always @* out=~in;

endmodule

module M2(input [31:0] in, output [31:0] out);

  assign out=~in;

endmodule

module main;
  wire [31:0] bin1, bin2;

  M1 m1(0, bin1);
  M2 m2(0, bin2);
  
  always assert property1: bin1=='hffffffff;
  always assert property2: bin2=='hffffffff;
  
endmodule
