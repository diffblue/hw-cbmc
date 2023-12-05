module main(input clk);

  // count down from 99 to 00, in binary coded decimals
  reg [3:0] digit1, digit2;

  initial digit1 = 9;
  initial digit2 = 9;

  always @(posedge clk) begin
    if(digit2 != 0)
      digit2 = digit2 - 1;
    else if(digit1 != 0) begin
      digit2 = 9;
      digit1 = digit1 - 1;
    end
  end

  // expected to pass with ranking function {digit1, digit2}
  p0: assert property (eventually digit1 == 0);

endmodule
