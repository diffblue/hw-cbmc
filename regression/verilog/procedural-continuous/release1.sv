module main(input clk);

  reg r;

  initial r = 0;

  always @(posedge clk)
  begin
    force r = 1;
    release r;
  end

endmodule
