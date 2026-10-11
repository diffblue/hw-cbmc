// FSM with time-multiplexed multiplier: computes (a*b + c*d) over 2 cycles
// Real hardware: 1 multiplier + 1 adder, shared across states
// Naive estimate: 2 multipliers + 1 adder (no sharing)
module fsm_shared_mult(
  input clk,
  input [15:0] a, b, c, d,
  output reg [31:0] result,
  output reg done
);
  reg state;
  reg [31:0] partial;

  always @(posedge clk) begin
    case (state)
      1'b0: begin
        partial <= a * b;
        done <= 1'b0;
        state <= 1'b1;
      end
      1'b1: begin
        result <= partial + c * d;
        done <= 1'b1;
        state <= 1'b0;
      end
    endcase
  end
endmodule
