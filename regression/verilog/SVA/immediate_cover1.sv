module main(input clk);

  reg [7:0] counter;

  initial counter = 0;

  always @(posedge clk)
    counter <= counter + 1;

  // expected to pass: counter reaches 5
  always @(posedge clk)
    p0: cover(counter == 5);

  // expected to fail: counter never reaches 200 within bound
  always @(posedge clk)
    p1: cover(counter == 200);

endmodule
