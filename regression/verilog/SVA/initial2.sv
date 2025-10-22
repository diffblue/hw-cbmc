module main(input clk);

  // count up from 0 to 10
  reg [7:0] counter;

  initial begin
    counter = 1;
    // expected to pass
    p0: assert(counter == 1);
    counter = 2;
  end

  // expected to pass
  initial p1: assert property (counter == 2);

  always_ff @(posedge clk)
    counter = counter + 1;

endmodule
