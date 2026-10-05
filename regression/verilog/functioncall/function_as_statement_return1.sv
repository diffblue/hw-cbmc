// A function with a `return <value>;` statement called as a statement,
// discarding its return value. Per IEEE 1800-2017 13.4.1, "a function
// can be called as a statement ...; the return value is discarded".
// The call still executes the body for its side effects, so after the
// first clock edge `side` must equal 3. ebmc currently rejects this with
// "return with value requires a function" during RTL construction.
module main(input clk);

  reg [3:0] side = 0;

  function automatic [3:0] f(input [3:0] x);
    side = x;
    return x + 1;
  endfunction

  // f is called as a statement; its return value is discarded, but the
  // body's side effect (side = x) still takes place.
  always @(posedge clk) f(4'd3);

  p0: assert property (@(posedge clk) ##1 side == 3);

endmodule
