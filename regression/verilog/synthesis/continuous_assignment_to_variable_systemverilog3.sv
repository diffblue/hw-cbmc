module main;

  logic [7:0] mask;

  genvar i;

  generate
    for (i=0; i<=7; i = i + 1) begin
       // Continuous assignment to variable,
       // allowed by SystemVerilog.
       assign mask[i] = (i%2)==1;
    end
  endgenerate

  assert final (mask == 'b10101010);

endmodule
