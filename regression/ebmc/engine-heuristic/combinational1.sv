module main(input x);

  reg y;

  // combinational only, no need to unwind
  always_comb @x begin : blk
    y = !x;
    p0: assert(x == !y);
  end

endmodule
