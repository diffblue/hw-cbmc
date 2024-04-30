module main(input [31:0] index);

  always @index begin
    if(index >= 10)
      assume(0);

    // should pass
    assert(index < 10);

    // should fail
    assert(0);
  end

endmodule
