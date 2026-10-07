module main(input clk, input [3:0] in1);

  reg [3:0] a, b, c;
  reg [3:0] cnt;

  initial begin
    a = 0; b = 0; c = 0; cnt = 0;
  end

  always @(posedge clk) begin
    a <= in1;
    b <= a;
    c <= b;
    cnt <= cnt + 1;
  end

  // cnt is not in the cone of p0, but this assumption is a general
  // constraint on cnt, and hence pulls cnt into the cone. The
  // assumption rules out all traces with more than three states.
  // If the definition of cnt were dropped, cnt would be unconstrained,
  // the assumption would be trivially satisfiable, and p0 would be
  // refuted in timeframe 3.
  a0: assume property (cnt < 4'd3);

  // c == 5 is first reachable in timeframe 3
  p0: assert property (c != 4'd5);

endmodule
