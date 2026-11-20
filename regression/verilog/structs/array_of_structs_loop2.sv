// A loop over a packed array of 64 packed structs in an always_comb,
// with member writes, whole-element writes and member reads of elements
// written by earlier iterations. The expressions for the arrays must
// grow linearly with the number of iterations; before, this design ran
// out of memory.
module main(input clk, input [8:0] lp);
  localparam N = 64;
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
    q[0] = {2'd0, 1'b0, 9'd0, 1'b1, 1'b0, 2'd1};
    q[1] = {2'd1, 1'b1, 9'd37, 1'b1, 1'b0, 2'd2};
    q[2] = {2'd2, 1'b1, 9'd74, 1'b1, 1'b0, 2'd3};
    q[3] = {2'd3, 1'b0, 9'd111, 1'b1, 1'b0, 2'd0};
    q[4] = {2'd0, 1'b1, 9'd148, 1'b1, 1'b0, 2'd1};
    q[5] = {2'd1, 1'b1, 9'd185, 1'b1, 1'b0, 2'd2};
    q[6] = {2'd2, 1'b0, 9'd222, 1'b1, 1'b0, 2'd3};
    q[7] = {2'd3, 1'b1, 9'd259, 1'b1, 1'b0, 2'd0};
    q[8] = {2'd0, 1'b1, 9'd296, 1'b1, 1'b0, 2'd1};
    q[9] = {2'd1, 1'b0, 9'd333, 1'b1, 1'b0, 2'd2};
    q[10] = {2'd2, 1'b1, 9'd370, 1'b1, 1'b0, 2'd3};
    q[11] = {2'd3, 1'b1, 9'd407, 1'b1, 1'b0, 2'd0};
    q[12] = {2'd0, 1'b0, 9'd444, 1'b1, 1'b0, 2'd1};
    q[13] = {2'd1, 1'b1, 9'd481, 1'b1, 1'b0, 2'd2};
    q[14] = {2'd2, 1'b1, 9'd18, 1'b1, 1'b0, 2'd3};
    q[15] = {2'd3, 1'b0, 9'd55, 1'b1, 1'b0, 2'd0};
    q[16] = {2'd0, 1'b1, 9'd92, 1'b1, 1'b0, 2'd1};
    q[17] = {2'd1, 1'b1, 9'd129, 1'b1, 1'b0, 2'd2};
    q[18] = {2'd2, 1'b0, 9'd166, 1'b1, 1'b0, 2'd3};
    q[19] = {2'd3, 1'b1, 9'd203, 1'b1, 1'b0, 2'd0};
    q[20] = {2'd0, 1'b1, 9'd240, 1'b1, 1'b0, 2'd1};
    q[21] = {2'd1, 1'b0, 9'd277, 1'b1, 1'b0, 2'd2};
    q[22] = {2'd2, 1'b1, 9'd314, 1'b1, 1'b0, 2'd3};
    q[23] = {2'd3, 1'b1, 9'd351, 1'b1, 1'b0, 2'd0};
    q[24] = {2'd0, 1'b0, 9'd388, 1'b1, 1'b0, 2'd1};
    q[25] = {2'd1, 1'b1, 9'd425, 1'b1, 1'b0, 2'd2};
    q[26] = {2'd2, 1'b1, 9'd462, 1'b1, 1'b0, 2'd3};
    q[27] = {2'd3, 1'b0, 9'd499, 1'b1, 1'b0, 2'd0};
    q[28] = {2'd0, 1'b1, 9'd36, 1'b1, 1'b0, 2'd1};
    q[29] = {2'd1, 1'b1, 9'd73, 1'b1, 1'b0, 2'd2};
    q[30] = {2'd2, 1'b0, 9'd110, 1'b1, 1'b0, 2'd3};
    q[31] = {2'd3, 1'b1, 9'd147, 1'b1, 1'b0, 2'd0};
    q[32] = {2'd0, 1'b1, 9'd184, 1'b1, 1'b0, 2'd1};
    q[33] = {2'd1, 1'b0, 9'd221, 1'b1, 1'b0, 2'd2};
    q[34] = {2'd2, 1'b1, 9'd258, 1'b1, 1'b0, 2'd3};
    q[35] = {2'd3, 1'b1, 9'd295, 1'b1, 1'b0, 2'd0};
    q[36] = {2'd0, 1'b0, 9'd332, 1'b1, 1'b0, 2'd1};
    q[37] = {2'd1, 1'b1, 9'd369, 1'b1, 1'b0, 2'd2};
    q[38] = {2'd2, 1'b1, 9'd406, 1'b1, 1'b0, 2'd3};
    q[39] = {2'd3, 1'b0, 9'd443, 1'b1, 1'b0, 2'd0};
    q[40] = {2'd0, 1'b1, 9'd480, 1'b1, 1'b0, 2'd1};
    q[41] = {2'd1, 1'b1, 9'd17, 1'b1, 1'b0, 2'd2};
    q[42] = {2'd2, 1'b0, 9'd54, 1'b1, 1'b0, 2'd3};
    q[43] = {2'd3, 1'b1, 9'd91, 1'b1, 1'b0, 2'd0};
    q[44] = {2'd0, 1'b1, 9'd128, 1'b1, 1'b0, 2'd1};
    q[45] = {2'd1, 1'b0, 9'd165, 1'b1, 1'b0, 2'd2};
    q[46] = {2'd2, 1'b1, 9'd202, 1'b1, 1'b0, 2'd3};
    q[47] = {2'd3, 1'b1, 9'd239, 1'b1, 1'b0, 2'd0};
    q[48] = {2'd0, 1'b0, 9'd276, 1'b1, 1'b0, 2'd1};
    q[49] = {2'd1, 1'b1, 9'd313, 1'b1, 1'b0, 2'd2};
    q[50] = {2'd2, 1'b1, 9'd350, 1'b1, 1'b0, 2'd3};
    q[51] = {2'd3, 1'b0, 9'd387, 1'b1, 1'b0, 2'd0};
    q[52] = {2'd0, 1'b1, 9'd424, 1'b1, 1'b0, 2'd1};
    q[53] = {2'd1, 1'b1, 9'd461, 1'b1, 1'b0, 2'd2};
    q[54] = {2'd2, 1'b0, 9'd498, 1'b1, 1'b0, 2'd3};
    q[55] = {2'd3, 1'b1, 9'd35, 1'b1, 1'b0, 2'd0};
    q[56] = {2'd0, 1'b1, 9'd72, 1'b1, 1'b0, 2'd1};
    q[57] = {2'd1, 1'b0, 9'd109, 1'b1, 1'b0, 2'd2};
    q[58] = {2'd2, 1'b1, 9'd146, 1'b1, 1'b0, 2'd3};
    q[59] = {2'd3, 1'b1, 9'd183, 1'b1, 1'b0, 2'd0};
    q[60] = {2'd0, 1'b0, 9'd220, 1'b1, 1'b0, 2'd1};
    q[61] = {2'd1, 1'b1, 9'd257, 1'b1, 1'b0, 2'd2};
    q[62] = {2'd2, 1'b1, 9'd294, 1'b1, 1'b0, 2'd3};
    q[63] = {2'd3, 1'b0, 9'd331, 1'b1, 1'b0, 2'd0};
  end

  always @(posedge clk) q <= q;

  always @(*) begin : B
    integer k;
    nq = q;
    nq2 = q;
    for(k = 0; k < N; k = k + 1) begin
      // member write
      if(nq[k].valid && nq[k].pseq <= lp)
        nq[k].hold_preq = 1'b0;
      // whole-element write, clearing the same bit
      if(nq2[k].valid && nq2[k].pseq <= lp)
        nq2[k] = nq2[k] & ~16'd8;
      // a member read of the previous element, written above
      if(k > 0)
        nq[k].hold_axi = nq[k-1].hold_preq;
    end
  end

  // lp = 300: entries 1, 2, 4 are cleared; entries 0, 3, 6 are not
  // valid, and entry 10 has pseq 370 > 300
  p0: assert property (@(posedge clk) lp == 9'd300 |->
    !nq[1].hold_preq && !nq[2].hold_preq && !nq[4].hold_preq &&
    nq[0].hold_preq && nq[3].hold_preq && nq[6].hold_preq &&
    nq[10].hold_preq);
  // both ways of writing agree, element by element
  p1: assert property (@(posedge clk)
    nq[1].hold_preq == nq2[1].hold_preq && nq[3].hold_preq == nq2[3].hold_preq &&
    nq[N-1].hold_preq == nq2[N-1].hold_preq);
  // the member read sees the previous element's new value
  p2: assert property (@(posedge clk) nq[2].hold_axi == nq[1].hold_preq);
  // the other members are unchanged
  p3: assert property (@(posedge clk) nq[N-1].pseq == 9'd331 && nq[N-1].tag == 2'd3);
  // fails: entry 1 is cleared when lp == 300
  p4: assert property (@(posedge clk) lp == 9'd300 |-> nq[1].hold_preq);
endmodule
