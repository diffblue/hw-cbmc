module main(input clk);

  reg r;

  initial r = 0;

  always @(posedge clk)
  begin
    assign r = 1;
    deassign r;
  end

endmodule
