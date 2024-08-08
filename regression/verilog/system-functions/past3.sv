module main(input clk);

  reg [31:0] counter = 0;

  always @(posedge clk)
    counter++;

  always @(posedge clk) begin
    // The for loop yields an elaboration-time constant,
    // which can be used for $past.
    integer i;
    for(i=0; i<10; i++)
      assert (counter == i -> $past(counter, i) == 0);
  end

endmodule
