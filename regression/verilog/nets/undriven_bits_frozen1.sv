module main(input clk);
  wire [7:0] v;
  assign v[7:4] = 4'd0;      // v[3:0] has no driver
  wire [3:0] w;              // w has no driver at all

  reg started = 0;
  reg [3:0] v_prev = 0, w_prev = 0;
  always @(posedge clk) begin
    started <= 1;
    v_prev  <= v[3:0];
    w_prev  <= w;
  end

  p_part:  assert property (@(posedge clk) !started || v[3:0] == v_prev);
  p_whole: assert property (@(posedge clk) !started || w == w_prev);
endmodule
