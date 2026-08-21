module main(input clk);

  generate
    if (1) begin : gen_block
      // IEEE 1800-2017 27.2: generate blocks may contain function
      // declarations; the function is usable within the scope of the
      // generate block.
      function automatic [7:0] plus_one(input [7:0] x);
        return x + 8'd1;
      endfunction

      wire [7:0] val = plus_one(8'd41);

      p1: assert property (@(posedge clk) val == 8'd42);
    end
  endgenerate

endmodule
