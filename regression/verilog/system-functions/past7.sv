module main(input clk);

  reg [7:0] counter = 0;

  always @(posedge clk) begin : blk
    counter++;
    p1: assert(counter == 1 -> $past(counter, 1) == 0);
    pn: assert(counter >= 2 -> $past(counter, 1) == counter - 2);
  end

endmodule
