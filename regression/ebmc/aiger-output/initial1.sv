// The initial values of the latches in AIGER output.
module main(input clk);
  reg r1, r2;
  initial r1 = 1;      // reset value 1
                       // r2: no initial value, i.e., any value
  always @(posedge clk) begin
    r1 <= r1;
    r2 <= r2;
  end
  p1: assert property (@(posedge clk) r1 == 1);  // holds
  p2: assert property (@(posedge clk) r2 == 0);  // fails
endmodule
