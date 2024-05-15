module main;

  reg [31:0] t;

  always @(*) begin
    t = 0;

    // out of bounds accesses are ignored
    t[0:-1] = 'b10;

    // should pass
    assert(t == 1);
  end

endmodule
