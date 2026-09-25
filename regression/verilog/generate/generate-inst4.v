// A module output port connected to a genvar-indexed bit of a vector
// inside a generate for-loop. The genvar must be evaluated with its
// per-iteration value when the port connection is elaborated; a regression
// (LogikBench blocks/lpddr5, blocks/chiplink, koios/bwave_like_*) used the
// stale post-loop genvar value, which mis-evaluated arr[g] (in particular
// the top index arr[WIDTH-1] was flagged out of bounds and folded to 0).
module child(output reg o);
endmodule

module main;

  wire [3:0] locked;

  genvar g;
  generate
    for(g = 0; g < 4; g = g + 1) begin: trn
      child u(.o(locked[g]));
    end
  endgenerate

endmodule
