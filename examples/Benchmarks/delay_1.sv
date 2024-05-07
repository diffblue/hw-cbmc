module DELAY #(localparam N = 750, localparam CBITS = 10) (input clk, input rst, output reg sig);
  reg [CBITS-1 :0] cnt;
  always @(posedge clk) begin
    if (rst) cnt = 0;
    else cnt = cnt + 1;
    if (cnt > N) begin sig = 1;
      cnt = 0; end
    else sig = 0;
  end
  p1: assert property  ((always s_eventually rst == 1) or (always s_eventually sig == 1)) ;
  // F G (rst = F) -> G F (sig = T)
endmodule
