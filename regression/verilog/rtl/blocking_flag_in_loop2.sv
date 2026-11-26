module main(input [31:0] in);

  // A priority encoder: the condition of each if reads the flag that the
  // previous iterations may have set. The definitions of out, valid and
  // found share the conditions.
  reg [31:0] out;
  reg valid, found;
  integer i;

  always @* begin
    out = 0;
    valid = 0;
    found = 0;
    for(i = 31; i >= 0; i = i - 1)
      if(!found && in[i]) begin
        out[i] = 1;
        valid = 1;
        found = 1;
      end
  end

  p0: assert final (valid == (in != 0));
  p1: assert final ($onehot0(out));

endmodule
