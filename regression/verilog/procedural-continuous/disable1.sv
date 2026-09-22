module main(input clk);

  reg r;

  initial r = 0;

  always @(posedge clk)
  begin : blk
    disable blk;
  end

endmodule
