// A register in a submodule that is read only through a continuous
// assignment to a wire (assign v = vr). The netlist-based engines read the
// wire out of step with the register, and refuted p0 (and the old IC3
// engine proved p1), until the netlist stopped taking the literals of
// symbols from the cache.
module sub(input clk, input rst_n, input push, input pop,
           output full, output empty);
  wire [1:0] v, v_nxt;
  reg  [1:0] vr;
  always @(posedge clk) if(!rst_n) vr <= 2'b00; else vr <= v_nxt;
  assign v = vr;
  assign v_nxt[0] = push | (pop ? v[1] : v[0]);
  assign v_nxt[1] = (v[1] & ~pop) | (push & v[0] & ~pop);
  assign empty = ~v[0];
  assign full  = v[1];
endmodule

module main(input clk, input push_in, input pop_in);
  reg rst_n = 0;
  always @(posedge clk) rst_n <= 1;
  wire full, empty;
  wire push = push_in & ~full & rst_n;
  wire pop  = pop_in & ~empty & rst_n;
  sub u(.clk(clk), .rst_n(rst_n), .push(push), .pop(pop), .full(full), .empty(empty));
  reg [1:0] occ = 0, occ2 = 0;
  always @(posedge clk) if(!rst_n) occ <= 0; else occ <= occ + push - pop;
  // miscounts a push, so p1 fails
  always @(posedge clk) if(!rst_n) occ2 <= 0; else occ2 <= occ2 + (push ? 2'd2 : 2'd0) - pop;
  p0: assert property (@(posedge clk) !rst_n || ((occ == 0) == empty));
  p1: assert property (@(posedge clk) !rst_n || ((occ2 == 0) == empty));
endmodule
