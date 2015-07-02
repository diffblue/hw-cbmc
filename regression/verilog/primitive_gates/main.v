module main(and_in1, and_in2, or_in1, or_in2, or_in3, buf_in, not_in);

  input [31:0] and_in1, and_in2;
  wire  [31:0] and_out;
  input [31:0] or_in1, or_in2, or_in3;
  wire  [31:0] or_out;
  input [31:0] buf_in;
  wire  [31:0] buf_out1, buf_out2, buf_out3;
  input [31:0] not_in;
  wire  [31:0] not_out;
  
  and a1[31:0] (and_out, and_in1, and_in2);
  or  o1[31:0] (or_out, or_in1, or_in2, or_in3);
  buf b1[31:0] (buf_out1, buf_out2, buf_in);
  buf b2[31:0] (buf_out3, buf_in);
  not n1[31:0] (not_out, not_in);
  
  always begin
    assert or_ok: (or_in1|or_in2|or_in3)==or_out;
    assert and_ok: (and_in1&and_in2)==and_out;
    assert buf_ok1: buf_in==buf_out1;
    assert buf_ok2: buf_in==buf_out2;
    assert buf_ok3: buf_in==buf_out3;
    assert not_ok: not_in==~not_out;
  end

endmodule
