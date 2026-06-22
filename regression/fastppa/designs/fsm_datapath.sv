// FSM with shared datapath: 4 states, single adder/shifter reused
module fsm_datapath(input clk, input [15:0] din, output reg [15:0] dout);
  reg [1:0] state;
  reg [15:0] acc;

  always @(posedge clk) begin
    case (state)
      2'd0: begin acc <= din + 16'd1;       state <= 2'd1; end
      2'd1: begin acc <= acc + din;          state <= 2'd2; end
      2'd2: begin acc <= acc << 1;           state <= 2'd3; end
      2'd3: begin dout <= acc; acc <= 16'd0; state <= 2'd0; end
    endcase
  end
endmodule
