module main(input clk);

  // count up from 0 to 10
  reg [7:0] counter;

  initial counter = 0;

  always @(posedge clk) begin
    // expected to pass
    p0: cover property (counter == 1);

    // expected to fail
    p1: cover property (counter == 100);

    if(counter == 10)
      counter = 0;
    else
      counter = counter + 1;
  end

endmodule
