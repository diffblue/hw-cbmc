// A loop over a packed array of packed structs in an always_comb, which
// reads members of the elements that earlier iterations may have written,
// and writes members or whole elements. The expressions for the array
// must not grow exponentially with the number of iterations.
module main(input clk, input [8:0] lp);
  localparam N = 4;
  typedef struct packed {
    logic [1:0] tag;
    logic valid;
    logic [8:0] pseq;
    logic hold_preq;
    logic hold_axi;
    logic [1:0] hold_tag;
  } s_t;

  s_t [N-1:0] q, nq, nq2;

  initial begin
    q[0] = {2'd1, 1'b1, 9'd5,   1'b1, 1'b0, 2'd2};
    q[1] = {2'd2, 1'b0, 9'd3,   1'b1, 1'b1, 2'd3};
    q[2] = {2'd3, 1'b1, 9'd100, 1'b1, 1'b0, 2'd0};
    q[3] = {2'd0, 1'b1, 9'd7,   1'b1, 1'b1, 2'd1};
  end

  always @(posedge clk) q <= q;

  always @(*) begin : B
    integer k;
    reg [8:0] tmp;
    nq = q;
    nq2 = q;
    for(k = 0; k < N; k = k + 1) begin
      // member write
      tmp = nq[k].pseq;
      if(nq[k].valid && tmp <= lp)
        nq[k].hold_preq = 1'b0;
      // whole-element write, clearing the same bit
      if(nq2[k].valid && nq2[k].pseq <= lp)
        nq2[k] = nq2[k] & ~16'd8;
    end
  end

  // lp = 6: entry 0 is valid with pseq 5 <= 6; entry 1 is not valid;
  // entries 2 and 3 have pseq > 6
  p0: assert property (@(posedge clk) lp == 9'd6 |->
    !nq[0].hold_preq && nq[1].hold_preq && nq[2].hold_preq && nq[3].hold_preq);
  p1: assert property (@(posedge clk) lp == 9'd200 |->
    !nq[0].hold_preq && nq[1].hold_preq && !nq[2].hold_preq && !nq[3].hold_preq);
  // the other members are unchanged
  p2: assert property (@(posedge clk) nq[2].pseq == 9'd100 && nq[1].tag == 2'd2);
  // both ways of writing agree
  p3: assert property (@(posedge clk) nq == nq2);
endmodule
