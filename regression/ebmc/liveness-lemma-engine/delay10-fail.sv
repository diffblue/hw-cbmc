module DELAY #(localparam N = 750, localparam CBITS = 10) (input clk, input rst, output reg sig);
  reg [CBITS-1 :0] cnt;
  reg [CBITS-1 :0] rank;

  always @(posedge clk) begin
    if (rst) cnt = 0;
    else cnt = cnt + 1;
    if (cnt > N) begin sig = 1;
      cnt = 0; end
    else sig = 0;
  end

  assign done = (rst || sig == 1);
  assign rank = N - cnt;

  // F G (rst = F) -> G F (sig = T)
  p1: assert property (@(posedge clk) s_eventually done) ;

  // does not hold -- too strong
  lemma: assert property(@(posedge clk) !done |=> rank < $past(rank));

endmodule
