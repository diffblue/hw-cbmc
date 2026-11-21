module main(input [15:0] in);

  // A priority encoder: the condition of each if reads the flag that the
  // previous iterations may have set.
  reg found;
  reg [15:0] out;
  integer i;

  always @* begin
    found = 0;
    out = 0;
    for(i = 15; i >= 0; i = i - 1)
      if(!found && in[i]) begin
        out[i] = 1;
        found = 1;
      end
  end

  p0: assert property (found == (in != 0));
  p1: assert property ($onehot0(out));

endmodule
