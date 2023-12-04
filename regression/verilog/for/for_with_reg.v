module main(input [7:0] data);

  reg [31:0] counter;
  reg is_zero;

  always @data begin
    is_zero = 1;
    for(counter = 0; counter < 8; counter = counter + 1)
      is_zero = is_zero && (data[counter] == 0);
  end

  always assert a1: is_zero == (data == 0);

endmodule
