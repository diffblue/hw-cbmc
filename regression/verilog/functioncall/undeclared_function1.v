module main(input in, output reg out);

  always @in begin
    out <= undeclared_function(in);
  end

endmodule
