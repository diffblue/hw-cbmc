module M1(out);
  output [31:0] out;
  reg [31:0] out;
  wire x;

  // genvar outside generate
  genvar i;

  generate
    for (i=0; i<31; i=i+1) begin:bit
      always @x
        out[i] = (i>=8);
    end
  endgenerate

endmodule

module M2(out);
  output [31:0] out;
  reg [31:0] out;
  wire x;
  
  generate
    // genvar inside generate
    genvar i;

    for (i=0; i<31; i=i+1) begin:bit
      always @x
        out[i] = (i>=8);
    end
  endgenerate

endmodule

module main;
  wire [31:0] bin1, bin2;

  M1 m1(bin1);
  M2 m2(bin2);
  
  always assert property1: bin1=='hff;
  always assert property2: bin2=='hff;

endmodule
