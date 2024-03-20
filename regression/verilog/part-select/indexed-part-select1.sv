module main(in);

  reg [31:0] out;
  input [7:0] in;
  
  always @in begin
    out[0 +: 8]=0;
    out[8 +: 8]=in;
    out[16 +: 16]=0;
  end

  p1: assert property ({ in, { 8 { 1'b0 }} } == out);

endmodule
