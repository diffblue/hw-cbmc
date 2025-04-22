module main(input clk, input [3:0] index);

  reg [31:0] t;

  always_ff @(posedge clk) begin
    // The LHS of the part select does not have to be constant.
    t[index*2 +: 2] = 'b01; 

    // should pass
    assert(t[index*2] == 1);
    assert(t[index*2+1] == 0);
  end

endmodule
