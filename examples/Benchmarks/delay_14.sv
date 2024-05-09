module DELAY #(localparam N = 100000, localparam CBITS = 17) (input clk, input rst, output reg sig);
  reg [CBITS-1 :0] cnt;
  always @(posedge clk) begin
    if (rst) cnt = 0;
    else cnt = cnt + 1;
    if (cnt > N) begin sig = 1;
      cnt = 0; end
    else sig = 0;
  end
  p1: assert property  (@(posedge clk) ((always s_eventually rst == 1) or (always s_eventually sig == 1))) ;
  // F G (rst = F) -> G F (sig = T)
endmodule
