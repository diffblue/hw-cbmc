module M;

  parameter some_parameter = 1;

endmodule

module main;

  generate
    genvar i;

    for(i = 0; i < 2; i = i + 1) begin : my_block
      M #(i) M_instance();
    end
  endgenerate

endmodule
